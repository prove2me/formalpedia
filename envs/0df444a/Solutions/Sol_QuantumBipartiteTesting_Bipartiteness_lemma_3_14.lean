-- Prove2me | solution 1 for QuantumBipartiteTesting.Bipartiteness.lemma_3_14
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T12:16:37.324823+00:00
-- url     : https://prove2.me/submissions/df3ec824-c770-4b53-9aaa-107ba96286c2

import Definitions.Def_QuantumBipartiteTesting_Bipartiteness_Reduction
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
namespace QuantumBipartiteTesting.Bipartiteness
open Finset
noncomputable section

private lemma geometric_product (d : ℕ) (z : Fin d → ℝ) (hz : ∀ i, |z i| < 1) :
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

private def indexBall (d J : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => range (J+1))).filter (fun κ => ∑ i, κ i ≤ J)

private lemma mem_indexBall (d J : ℕ) (κ : Fin d → ℕ) :
    κ ∈ indexBall d J ↔ ∑ i, κ i ≤ J := by
  classical
  simp only [indexBall, mem_filter, Fintype.mem_piFinset, mem_range]
  constructor
  · exact And.right
  · intro h
    refine ⟨fun i => ?_,h⟩
    have : κ i ≤ ∑ j, κ j := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)
    omega

private lemma geometric_tail (d J : ℕ) (z : Fin d → ℝ) (hz : ∀ i, |z i| ≤ 1/4) :
    |(∏ i, (1-z i)⁻¹) - ∑ κ ∈ indexBall d J, ∏ i, z i ^ κ i| ≤
      (1/2 : ℝ)^(J+1) * 2^d := by
  classical
  let f := fun κ : Fin d → ℕ => ∏ i, z i ^ κ i
  let g := fun κ : Fin d → ℕ => ∏ i, (2*|z i|) ^ κ i
  have hf := geometric_product d z (fun i => lt_of_le_of_lt (hz i) (by norm_num))
  have hg := geometric_product d (fun i => 2*|z i|) (by
    intro i
    rw [abs_of_nonneg (by positivity)]
    have := hz i
    linarith)
  have hgpos : ∀ κ, 0 ≤ g κ := fun κ => prod_nonneg (fun i _ => by positivity)
  have hgnorm : (∑' κ, g κ) ≤ (2 : ℝ)^d := by
    rw [hg.tsum_eq]
    calc
      _ ≤ ∏ i : Fin d, (2 : ℝ) := by
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
  have hpoint : ∀ κ : {κ : Fin d → ℕ // κ ∉ indexBall d J},
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
  have hsplit := hf.summable.sum_add_tsum_subtype_compl (indexBall d J)
  rw [hf.tsum_eq] at hsplit
  have heq : (∏ i, (1-z i)⁻¹) - ∑ κ ∈ indexBall d J, f κ =
      ∑' κ : {κ : Fin d → ℕ // κ ∉ indexBall d J}, f κ.val := by linarith
  change |(∏ i, (1-z i)⁻¹) - ∑ κ ∈ indexBall d J, f κ| ≤ _
  rw [heq, ← Real.norm_eq_abs]
  calc
    _ ≤ ∑' κ : {κ : Fin d → ℕ // κ ∉ indexBall d J}, ‖f κ.val‖ :=
      norm_tsum_le_tsum_norm (hf.summable.norm.subtype _)
    _ ≤ ∑' κ : {κ : Fin d → ℕ // κ ∉ indexBall d J}, (1/2 : ℝ)^(J+1) * g κ.val :=
      (hf.summable.norm.subtype _).tsum_le_tsum hpoint ((hg.summable.subtype _).mul_left _)
    _ = (1/2 : ℝ)^(J+1) * ∑' κ : {κ : Fin d → ℕ // κ ∉ indexBall d J}, g κ.val :=
      (hg.summable.subtype _).tsum_mul_left _
    _ ≤ (1/2 : ℝ)^(J+1) * ∑' κ, g κ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Summable.tsum_subtype_le g _ hgpos hg.summable
    _ ≤ _ := mul_le_mul_of_nonneg_left hgnorm (by positivity)

private lemma truncated_degree (d J : ℕ) (z : Fin d → Bivariate)
    (hz : ∀ i, (z i).totalDegree ≤ 1) :
    (∑ κ ∈ indexBall d J, ∏ i, z i ^ κ i).totalDegree ≤ J := by
  apply (MvPolynomial.totalDegree_finsetSum _ _).trans
  apply Finset.sup_le
  intro κ hκ
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  apply (sum_le_sum (fun i _ => ?_)).trans ((mem_indexBall d J κ).mp hκ)
  calc
    _ ≤ κ i * (z i).totalDegree := MvPolynomial.totalDegree_pow _ _
    _ ≤ κ i * 1 := Nat.mul_le_mul_left _ (hz i)
    _ = _ := mul_one _

private lemma relative_error (d : ℕ) (z : Fin d → ℝ) (hz : ∀ i, |z i| ≤ 1/4) :
    |(∏ i, (1-z i)) * (∑ κ ∈ indexBall d (4*d+10), ∏ i, z i ^ κ i) - 1| ≤ 1/100 := by
  have hfactor : ∀ i, 0 < 1-z i := by
    intro i
    have := (abs_le.mp (hz i)).2
    linarith
  have hp : (∏ i, (1-z i)) ≠ 0 := prod_ne_zero_iff.mpr (fun i _ => (hfactor i).ne')
  have hi : (∏ i, (1-z i)) * (∏ i, (1-z i)⁻¹) = 1 := by
    rw [prod_inv_distrib, mul_inv_cancel₀ hp]
  have hbound : |∏ i, (1-z i)| ≤ (5/4 : ℝ)^d := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ i : Fin d, (5/4 : ℝ) := by
        apply prod_le_prod (fun _ _ => abs_nonneg _)
        intro i hi
        calc
          _ ≤ |(1 : ℝ)| + |z i| := abs_sub _ _
          _ ≤ _ := by norm_num; linarith [hz i]
      _ = _ := by simp [div_pow]
  calc
    _ = |∏ i, (1-z i)| *
        |(∑ κ ∈ indexBall d (4*d+10), ∏ i, z i ^ κ i) - ∏ i, (1-z i)⁻¹| := by
      rw [← abs_mul, mul_sub, hi]
    _ ≤ (5/4 : ℝ)^d * ((1/2 : ℝ)^((4*d+10)+1) * 2^d) := by
      apply mul_le_mul hbound _ (abs_nonneg _) (by positivity)
      rw [abs_sub_comm]
      exact geometric_tail d (4*d+10) z hz
    _ = (5/32 : ℝ)^d * (1/2 : ℝ)^11 := by
      rw [show 4*d+10+1 = 4*d+11 by omega, pow_add, pow_mul]
      rw [show (1/2 : ℝ)^4 = 1/16 by norm_num]
      rw [show (5/32 : ℝ)^d = ((5/4 : ℝ) * (1/16) * 2)^d by norm_num]
      simp only [mul_pow]
      ring
    _ ≤ 1 * (1/2 : ℝ)^11 := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact pow_le_one₀ (by norm_num) (by norm_num)
    _ ≤ _ := by norm_num

end
end QuantumBipartiteTesting.Bipartiteness

open QuantumBipartiteTesting.Bipartiteness Finset

theorem solution (d : ℕ) (z : Fin d → Bivariate)
    (haffine : ∀ i, (z i).totalDegree ≤ 1) (C : ℝ) (hC : 0 < C) (region : Set (ℝ × ℝ))
    (hz : ∀ x ∈ region, ∀ i, |Eval (z i) x.1 x.2| ≤ 1/4) :
    ∃ A : Bivariate, A.totalDegree ≤ 4*d+10 ∧
      ∀ x ∈ region, |Eval (MvPolynomial.C C * ∏ i, (1-z i)) x.1 x.2 * Eval A x.1 x.2 - 1| ≤ 1/100 := by
  classical
  refine ⟨MvPolynomial.C C⁻¹ * ∑ κ ∈ indexBall d (4*d+10), ∏ i, z i ^ κ i, ?_, ?_⟩
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    simpa only [MvPolynomial.totalDegree_C, zero_add] using truncated_degree d (4*d+10) z haffine
  · intro x hx
    have he := relative_error d (fun i => Eval (z i) x.1 x.2) (hz x hx)
    simpa only [Eval, map_mul, map_prod, map_sum, map_sub, map_one, MvPolynomial.eval_C,
      map_pow, mul_assoc, mul_left_comm, mul_inv_cancel_left₀ hC.ne'] using he
