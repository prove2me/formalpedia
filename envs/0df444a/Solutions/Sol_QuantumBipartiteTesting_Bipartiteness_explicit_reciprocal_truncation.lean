-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.explicit_reciprocal_truncation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:26:18.054661+00:00
-- url     : https://prove2.me/submissions/6ab991e5-8860-46ad-884a-6762abdc3c0c

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

private lemma geometric_product_fin (d : ℕ) (z : Fin d → ℝ) (hz : ∀ i, |z i| < 1) :
    HasSum (fun κ : Fin d → ℕ => ∏ i, z i ^ κ i) (∏ i, (1-z i)⁻¹) := by
  induction d with
  | zero =>
    simpa using (hasSum_fintype (fun κ : Fin 0 → ℕ => (1 : ℝ)))
  | succ d ih =>
    have h₀ := hasSum_geometric_of_abs_lt_one (hz 0)
    have ht := ih (fun i => z i.succ) (fun i => hz i.succ)
    have hs₀ : Summable (fun j : ℕ => ‖z 0 ^ j‖) := h₀.summable.norm
    have hst : Summable (fun κ : Fin d → ℕ => ‖∏ i, z i.succ ^ κ i‖) := ht.summable.norm
    have hp : HasSum (fun p : ℕ × (Fin d → ℕ) => z 0 ^ p.1 * ∏ i, z i.succ ^ p.2 i)
        ((1-z 0)⁻¹ * ∏ i : Fin d, (1-z i.succ)⁻¹) :=
      HasSum.mul (ι := ℕ) (κ := Fin d → ℕ) (α := ℝ)
        (f := fun j : ℕ => z 0 ^ j) (g := fun κ : Fin d → ℕ => ∏ i, z i.succ ^ κ i)
        (s := (1-z 0)⁻¹) (t := ∏ i : Fin d, (1-z i.succ)⁻¹) h₀ ht
        (summable_mul_of_summable_norm
        (f := fun j : ℕ => z 0 ^ j) (g := fun κ : Fin d → ℕ => ∏ i, z i.succ ^ κ i) hs₀ hst)
    apply (Fin.consEquiv (fun _ : Fin (d+1) => ℕ)).hasSum_iff.mp
    simpa [Function.comp_def, Fin.prod_univ_succ, mul_comm] using hp

private lemma geometric_product {I : Type} [Fintype I] (z : I → ℝ) (hz : ∀ i, |z i| < 1) :
    HasSum (fun κ : I → ℕ => ∏ i, z i ^ κ i) (∏ i, (1-z i)⁻¹) := by
  let e := Fintype.equivFin I
  have h := geometric_product_fin (Fintype.card I) (fun i => z (e.symm i)) (fun i => hz _)
  apply (Equiv.arrowCongr e.symm (Equiv.refl ℕ)).hasSum_iff.mp
  simpa only [Function.comp_def, Equiv.arrowCongr_apply, Equiv.refl_apply, Equiv.symm_symm, Equiv.apply_symm_apply,
    ← e.symm.prod_comp] using h

private def indexBall (I : Type) [Fintype I] (J : ℕ) : Finset (I → ℕ) :=
  (Fintype.piFinset (fun _ : I => range (J+1))).filter (fun κ => ∑ i, κ i ≤ J)

private lemma mem_indexBall (I : Type) [Fintype I] (J : ℕ) (κ : I → ℕ) :
    κ ∈ indexBall I J ↔ ∑ i, κ i ≤ J := by
  simp only [indexBall, mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨fun i => ?_,h⟩
    have : κ i ≤ ∑ j, κ j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega

private lemma geometric_tail {I : Type} [Fintype I] (J : ℕ) (z : I → ℝ) (hz : ∀ i, |z i| ≤ 1/4) :
    |(∏ i, (1-z i)⁻¹) - ∑ κ ∈ indexBall I J, ∏ i, z i ^ κ i| ≤
      (1/2 : ℝ)^(J+1) * 2^(Fintype.card I) := by
  let f := fun κ : I → ℕ => ∏ i, z i ^ κ i
  let g := fun κ : I → ℕ => ∏ i, (2*|z i|) ^ κ i
  have hf := geometric_product z (fun i => lt_of_le_of_lt (hz i) (by norm_num))
  have hg := geometric_product (fun i => 2*|z i|) (by
    intro i
    rw [abs_of_nonneg (by positivity)]
    have := hz i
    linarith)
  have hgpos : ∀ κ, 0 ≤ g κ := fun κ => prod_nonneg (fun i _ => by positivity)
  have hgnorm : (∑' κ, g κ) ≤ (2 : ℝ)^(Fintype.card I) := by
    rw [hg.tsum_eq]
    calc
      _ ≤ ∏ i : I, (2 : ℝ) := by
        apply prod_le_prod
        · intro i hi
          apply inv_nonneg.mpr
          have := hz i
          linarith
        · intro i hi
          apply (inv_le_comm₀ (by have := hz i; linarith) (by norm_num)).mpr
          have := hz i
          norm_num
          linarith
      _ = _ := by simp
  have hpoint : ∀ κ : {κ : I → ℕ // κ ∉ indexBall I J},
      ‖f κ.val‖ ≤ (1/2 : ℝ)^(J+1) * g κ.val := by
    intro κ
    have hdegree : J+1 ≤ ∑ i, κ.val i := by
      have := κ.property
      rw [mem_indexBall] at this
      omega
    have heq : ‖f κ.val‖ = (1/2 : ℝ)^(∑ i, κ.val i) * g κ.val := by
      dsimp [f,g]
      rw [← prod_pow_eq_pow_sum, ← prod_mul_distrib, Finset.abs_prod]
      apply prod_congr rfl
      intro i hi
      rw [abs_pow, ← mul_pow]
      congr 1
      ring
    rw [heq]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one (by norm_num) (by norm_num) hdegree)
      (hgpos _)
  have hsplit := hf.summable.sum_add_tsum_subtype_compl (indexBall I J)
  rw [hf.tsum_eq] at hsplit
  have heq : (∏ i, (1-z i)⁻¹) - ∑ κ ∈ indexBall I J, f κ =
      ∑' κ : {κ : I → ℕ // κ ∉ indexBall I J}, f κ.val := by linarith
  change |(∏ i, (1-z i)⁻¹) - ∑ κ ∈ indexBall I J, f κ| ≤ _
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' κ : {κ : I → ℕ // κ ∉ indexBall I J}, ‖f κ.val‖ :=
      norm_tsum_le_tsum_norm (hf.summable.norm.subtype _)
    _ ≤ ∑' κ : {κ : I → ℕ // κ ∉ indexBall I J}, (1/2 : ℝ)^(J+1) * g κ.val :=
      (hf.summable.norm.subtype _).tsum_le_tsum hpoint ((hg.summable.subtype _).mul_left _)
    _ = (1/2 : ℝ)^(J+1) * ∑' κ : {κ : I → ℕ // κ ∉ indexBall I J}, g κ.val :=
      (hg.summable.subtype _).tsum_mul_left _
    _ ≤ (1/2 : ℝ)^(J+1) * ∑' κ, g κ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Summable.tsum_subtype_le g _ hgpos hg.summable
    _ ≤ _ := mul_le_mul_of_nonneg_left hgnorm (by positivity)

private lemma truncated_degree {I : Type} [Fintype I] (J : ℕ) (z : I → Bivariate)
    (hz : ∀ i, (z i).totalDegree ≤ 1) :
    (∑ κ ∈ indexBall I J, ∏ i, z i ^ κ i).totalDegree ≤ J := by
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro κ hκ
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply (sum_le_sum (fun i _ => ?_)).trans ((mem_indexBall I J κ).mp hκ)
  calc
    _ ≤ κ i * (z i).totalDegree := MvPolynomial.totalDegree_pow _ _
    _ ≤ κ i * 1 := Nat.mul_le_mul_left _ (hz i)
    _ = _ := mul_one _

private lemma relative_error {I : Type} [Fintype I] (z : I → ℝ) (hz : ∀ i, |z i| ≤ 1/4) :
    |(∏ i, (1-z i)) * (∑ κ ∈ indexBall I (4*Fintype.card I+10), ∏ i, z i ^ κ i) - 1| ≤ 1/100 := by
  have hfactor : ∀ i, 0 < 1-z i := by
    intro i
    have := (abs_le.mp (hz i)).2
    linarith
  have hp : (∏ i, (1-z i)) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => (hfactor i).ne')
  have hi : (∏ i, (1-z i)) * (∏ i, (1-z i)⁻¹) = 1 := by
    rw [prod_inv_distrib, mul_inv_cancel₀ hp]
  have hbound : |∏ i, (1-z i)| ≤ (5/4 : ℝ)^(Fintype.card I) := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ i : I, (5/4 : ℝ) := by
        apply prod_le_prod (fun _ _ => abs_nonneg _)
        intro i hi
        calc
          _ ≤ |(1 : ℝ)| + |z i| := abs_sub _ _
          _ ≤ _ := by norm_num; linarith [hz i]
      _ = _ := by simp [div_pow]
  calc
    _ = |∏ i, (1-z i)| *
        |(∑ κ ∈ indexBall I (4*Fintype.card I+10), ∏ i, z i ^ κ i) - ∏ i, (1-z i)⁻¹| := by
      rw [← abs_mul, mul_sub, hi]
    _ ≤ (5/4 : ℝ)^(Fintype.card I) * ((1/2 : ℝ)^((4*Fintype.card I+10)+1) * 2^(Fintype.card I)) := by
      apply mul_le_mul hbound _ (abs_nonneg _) (by positivity)
      rw [abs_sub_comm]
      exact geometric_tail (4*Fintype.card I+10) z hz
    _ = (5/32 : ℝ)^(Fintype.card I) * (1/2 : ℝ)^11 := by
      rw [show 4*Fintype.card I+10+1 = 4*Fintype.card I+11 by omega, pow_add, pow_mul]
      rw [show (1/2 : ℝ)^4 = 1/16 by norm_num]
      rw [show (5/32 : ℝ)^(Fintype.card I) = ((5/4 : ℝ) * (1/16) * 2)^(Fintype.card I) by norm_num]
      simp only [mul_pow]
      ring
    _ ≤ 1 * (1/2 : ℝ)^11 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_one₀ (by norm_num) (by norm_num)
    _ ≤ _ := by norm_num

private lemma homogeneous_ball {I : Type} [Fintype I]
    (z : I → Bivariate) (j : ℕ) :
    Homogeneous z j = ∑ κ ∈ (indexBall I j).filter (fun κ => ∑ i, κ i = j), ∏ i, z i ^ κ i := by
  unfold Homogeneous
  rw [← sum_filter]
  apply sum_bij (fun κ _ => fun i => (κ i).val)
  · intro κ hκ
    have heq : ∑ i, (κ i).val = j := (mem_filter.mp hκ).2
    exact mem_filter.mpr ⟨(mem_indexBall I j _).mpr heq.le, heq⟩
  · intro κ hκ η hη heq
    funext i
    exact Fin.ext (congrFun heq i)
  · intro κ hκ
    have heq : ∑ i, κ i = j := (mem_filter.mp hκ).2
    have hbound : ∀ i, κ i < j+1 := by
      intro i
      have hsum : κ i ≤ ∑ a, κ a := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
      omega
    let η : I → Fin (j+1) := fun i => ⟨κ i,hbound i⟩
    refine ⟨η, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
    exact heq
  · intro κ hκ
    rfl

private lemma truncated_homogeneous {I : Type} [Fintype I]
    (z : I → Bivariate) (J : ℕ) :
    ∑ j ∈ range (J+1), Homogeneous z j = ∑ κ ∈ indexBall I J, ∏ i, z i ^ κ i := by
  calc
    _ = ∑ j ∈ range (J+1), ∑ κ ∈ (indexBall I J).filter (fun κ => ∑ i, κ i = j),
        ∏ i, z i ^ κ i := by
      apply sum_congr rfl
      intro j hj
      rw [homogeneous_ball]
      congr 1
      ext κ
      simp only [mem_filter, mem_indexBall]
      have : j ≤ J := Nat.le_of_lt_succ (mem_range.mp hj)
      omega
    _ = _ := sum_fiberwise_of_maps_to (fun κ hκ => mem_range.mpr
      (Nat.lt_succ_of_le ((mem_indexBall I J _).mp hκ))) _

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness Finset
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I : Type} [Fintype I] (z : I → Bivariate)
    (haffine : ∀ i, (z i).totalDegree ≤ 1) (C : ℝ) (hC : 0 < C) :
    (MvPolynomial.C C⁻¹ * ∑ j ∈ range (4*Fintype.card I+11), Homogeneous z j).totalDegree ≤
      4*Fintype.card I+10 ∧
    ∀ M l : ℝ, (∀ i, |Eval (z i) M l| ≤ 1/4) →
      |Eval (MvPolynomial.C C * ∏ i, (1-z i)) M l *
        Eval (MvPolynomial.C C⁻¹ * ∑ j ∈ range (4*Fintype.card I+11), Homogeneous z j) M l - 1| ≤ 1/100 := by
  rw [show 4*Fintype.card I+11 = (4*Fintype.card I+10)+1 by omega, truncated_homogeneous]
  constructor
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simpa only [MvPolynomial.totalDegree_C, zero_add] using
      truncated_degree (4*Fintype.card I+10) z haffine
  · intro M l hz
    have he := relative_error (fun i => Eval (z i) M l) hz
    simpa only [Eval, map_mul, map_prod, map_sum, map_sub, map_one, MvPolynomial.eval_C,
      map_pow, mul_assoc, mul_left_comm, mul_inv_cancel_left₀ hC.ne'] using he
