-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P38.purifiedOutput_blockDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:32:18.303372+00:00
-- url     : https://prove2.me/submissions/73e826a0-b4c3-471e-a7d0-0807445cdd89

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P38
noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Claimed50 QAlgorithms.Papers.Independent.Claimed50.P38

open scoped ComplexConjugate Matrix

open Filter

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

section G68ILIB
open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P38
open scoped ComplexConjugate Matrix ComplexOrder
open QAlgorithms.Papers.Independent.Information100.P58 (Word)

lemma g68i_tens_single {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    (M : Superop A A) (u v α β : A × B) :
    tensorSuperop M (completeDephasing (A := B)) (Matrix.single u v 1) α β =
      M (Matrix.single u.1 v.1 1) α.1 β.1 *
        (if u.2 = α.2 ∧ v.2 = β.2 ∧ α.2 = β.2 then 1 else 0) := by
  unfold tensorSuperop
  rw [Finset.sum_eq_single u, Finset.sum_eq_single v]
  · simp only [Matrix.single_apply_same, one_mul, completeDephasing]
    by_cases h : α.2 = β.2
    · simp only [h, if_true, Matrix.single_apply]
      by_cases h1 : u.2 = β.2 <;> by_cases h2 : v.2 = β.2 <;> simp [h1, h2, eq_comm]
    · simp [h]
  · intro j _ hj; simp [Matrix.single_apply, Ne.symm hj]
  · intro h; simp at h
  · intro i _ hi
    refine Finset.sum_eq_zero (fun j _ => ?_)
    simp [Matrix.single_apply, Ne.symm hi]
  · intro h; simp at h

lemma g68i_pi_smul {ι κ : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι κ) (c : ℂ) (X : Matrix (Fin k → ι) (Fin k → ι) ℂ) :
    piSuperop Φ (c • X) = c • piSuperop Φ X := by
  ext y y'
  simp only [piSuperop, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

lemma g68i_pi_zero {ι κ : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (Φ : Fin k → Superop ι κ) :
    piSuperop Φ (0 : Matrix (Fin k → ι) (Fin k → ι) ℂ) = 0 := by
  ext y y'
  simp [piSuperop]

lemma g68i_deph_apply {d delta n : ℕ} (M : Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (a b : Word n d × Word n delta) :
    dephasedPower M n R a b =
      if a.2 = b.2 then piSuperop (fun _ : Fin n => M) (conditionalBlock R a.2) a.1 b.1 else 0 := by
  unfold dephasedPower piSuperop
  simp only [Matrix.of_apply, g68i_tens_single, Finset.prod_mul_distrib, Finset.prod_boole]
  let e : (Word n d × Word n delta) ≃ (Fin n → Fin d × Fin delta) :=
    { toFun := fun p k => (p.1 k, p.2 k), invFun := fun x => (fun k => (x k).1, fun k => (x k).2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  rw [← e.sum_comp]
  simp_rw [← e.sum_comp (fun x => _ * _)]
  simp only [e, Equiv.coe_fn_mk, Finset.mem_univ, true_implies]
  have hc : ∀ p q : Word n d × Word n delta,
      (∀ i, p.2 i = a.2 i ∧ q.2 i = b.2 i ∧ a.2 i = b.2 i) ↔ (p.2 = a.2 ∧ q.2 = b.2 ∧ a.2 = b.2) := by
    intro p q
    simp only [funext_iff, forall_and]
  simp only [hc, Fintype.sum_prod_type]
  split_ifs with h
  · refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [Fintype.sum_eq_single a.2 (fun x1 hx1 => Finset.sum_eq_zero (fun x2 _ =>
      Finset.sum_eq_zero (fun x3 _ => by simp [hx1])))]
    refine Finset.sum_congr rfl (fun x2 _ => ?_)
    rw [Fintype.sum_eq_single b.2 (fun x3 hx3 => by simp [hx3])]
    simp [h, conditionalBlock]
  · simp [h]

open scoped ComplexOrder in
lemma g68i_block_psd {A B : Type*} [Fintype A] [Fintype B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (b : B) :
    (conditionalBlock R b).PosSemidef := by
  have : conditionalBlock R b = R.submatrix (fun i => (i, b)) (fun i => (i, b)) := rfl
  rw [this]; exact hR.submatrix _

open scoped ComplexOrder in
lemma g68i_weight_nonneg {A B : Type*} [Fintype A] [Fintype B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (b : B) : 0 ≤ branchWeight R b := by
  have := (g68i_block_psd R hR b).trace_nonneg
  exact (Complex.nonneg_iff.1 this).1

open scoped ComplexOrder in
lemma g68i_block_zero {A B : Type*} [Fintype A] [Fintype B]
    (R : Matrix (A × B) (A × B) ℂ) (hR : R.PosSemidef) (b : B) (hw : ¬ 0 < branchWeight R b) :
    conditionalBlock R b = 0 := by
  have hP := g68i_block_psd R hR b
  have h0 : branchWeight R b = 0 := le_antisymm (not_lt.1 hw) (g68i_weight_nonneg R hR b)
  have ht := hP.trace_nonneg
  rw [Complex.nonneg_iff] at ht
  apply hP.trace_eq_zero_iff.1
  apply Complex.ext
  · simpa [branchWeight] using h0
  · simpa using ht.2.symm

lemma g68i_weight_smul {d delta n : ℕ} (Φ : Fin n → Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ) (hR : R.PosSemidef)
    (a0 : Word n d) (c : Word n delta) :
    (branchWeight R c : ℂ) • piSuperop Φ (conditionalState a0 R c) =
      piSuperop Φ (conditionalBlock R c) := by
  unfold conditionalState
  split_ifs with h
  · rw [g68i_pi_smul, smul_smul, mul_inv_cancel₀ (by exact_mod_cast h.ne'), one_smul]
  · have h0 : branchWeight R c = 0 := le_antisymm (not_lt.1 h) (g68i_weight_nonneg R hR c)
    rw [g68i_block_zero R hR c h, h0, g68i_pi_zero]
    simp

lemma g68i_pure_ket {B : Type*} [DecidableEq B] (c x y : B) :
    pureDensity (ket c) x y = if x = c ∧ y = c then 1 else 0 := by
  simp only [pureDensity, ket, Matrix.of_apply]
  by_cases hx : x = c <;> by_cases hy : y = c <;> simp [hx, hy, EuclideanSpace.single_apply]

theorem g68i_deph_block (d delta n : ℕ)
    (M : Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R) (a0 : Word n d) :
    dephasedPower M n R = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b))
        (pureDensity (ket b)) := by
  ext ⟨a1, a2⟩ ⟨b1, b2⟩
  rw [g68i_deph_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, g68i_pure_ket,
    smul_eq_mul]
  rw [Fintype.sum_eq_single a2 (fun c hc => by simp [Ne.symm hc])]
  by_cases h1 : a2 = b2
  · subst h1
    simp only [and_self, if_true, mul_one, if_pos rfl]
    rw [← g68i_weight_smul _ R hR.1 a0]
    simp [Matrix.smul_apply]
  · simp [h1, Ne.symm h1]

lemma g68i_withRef_apply {A C : Type*} (f : Superop A A) (X : Matrix (A × C) (A × C) ℂ)
    (x y : A × C) :
    withReference f X x y = f (Matrix.of fun i i' => X (i, x.2) (i', y.2)) x.1 y.1 := rfl

lemma g68i_purified_apply {d delta n : ℕ} {C : Type*} (M : Superop (Fin d) (Fin d))
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (a b : (Word n d × C) × Word n delta) :
    purifiedOutput M n psi a b = if a.2 = b.2 then piSuperop (fun _ : Fin n => M)
      (Matrix.of fun x x' => psi ((x, a.2), a.1.2) * conj (psi ((x', a.2), b.1.2))) a.1.1 b.1.1
      else 0 := by
  unfold purifiedOutput
  rw [g68i_withRef_apply, g68i_deph_apply]
  rfl

lemma g68i_weight_psi {d delta n : ℕ} {C : Type*} [Fintype C]
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (b : Word n delta) :
    branchWeight R b = ∑ x : Word n d, ∑ c : C, Complex.normSq (psi ((x, b), c)) := by
  rw [← hpurifies]
  simp only [branchWeight, conditionalBlock, Matrix.trace, Matrix.diag_apply, traceRight,
    pureDensity, Matrix.of_apply, Complex.re_sum, Complex.mul_conj, Complex.ofReal_re]

lemma g68i_psi_zero {d delta n : ℕ} {C : Type*} [Fintype C]
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (b : Word n delta)
    (hw : ¬ 0 < branchWeight R b) (x : Word n d) (c : C) : psi ((x, b), c) = 0 := by
  rw [g68i_weight_psi R psi hpurifies b] at hw
  have h0 : ∑ x : Word n d, ∑ c : C, Complex.normSq (psi ((x, b), c)) = 0 :=
    le_antisymm (not_lt.1 hw) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Complex.normSq_nonneg _)))
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Finset.sum_nonneg
      (fun _ _ => Complex.normSq_nonneg _))] at h0
  have h1 := h0 x (Finset.mem_univ _)
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Complex.normSq_nonneg _)] at h1
  exact Complex.normSq_eq_zero.1 (h1 c (Finset.mem_univ _))

lemma g68i_purif_smul {d delta n : ℕ} {C : Type*} [Fintype C] [DecidableEq C]
    (Φ : Fin n → Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R) (a0 : Word n d) (c0 : C)
    (b : Word n delta) (c c' : C) :
    (branchWeight R b : ℂ) • piSuperop Φ (Matrix.of fun x x' =>
        pureDensity (conditionalPurification a0 c0 R psi b) (x, c) (x', c')) =
      piSuperop Φ (Matrix.of fun x x' => psi ((x, b), c) * conj (psi ((x', b), c'))) := by
  rw [← g68i_pi_smul]
  congr 1
  ext x x'
  simp only [Matrix.smul_apply, Matrix.of_apply, pureDensity, conditionalPurification, smul_eq_mul]
  split_ifs with h
  · have hs : ((Real.sqrt (branchWeight R b) : ℂ)) ^ 2 = (branchWeight R b : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt h.le]
    have hs0 : ((Real.sqrt (branchWeight R b) : ℂ)) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.2 h).ne'
    simp only [PiLp.toLp_apply, map_div₀, Complex.conj_ofReal]
    rw [← hs]
    field_simp
  · rw [g68i_psi_zero R psi hpurifies b h x c]
    have h0 : branchWeight R b = 0 := by
      rw [g68i_weight_psi R psi hpurifies b]
      refine Finset.sum_eq_zero (fun x _ => Finset.sum_eq_zero (fun c _ => ?_))
      rw [g68i_psi_zero R psi hpurifies b h x c]; simp
    simp [h0]

theorem g68i_purif_block (d delta n : ℕ) {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d))
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    purifiedOutput M n psi = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (withReference (piSuperop (fun _ : Fin n => M))
          (pureDensity (conditionalPurification a0 c0 R psi b)))
        (pureDensity (ket b)) := by
  ext ⟨⟨a1, c⟩, a2⟩ ⟨⟨b1, c'⟩, b2⟩
  rw [g68i_purified_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.kronecker, Matrix.kroneckerMap_apply, g68i_pure_ket,
    smul_eq_mul]
  rw [Fintype.sum_eq_single a2 (fun c hc => by simp [Ne.symm hc])]
  by_cases h1 : a2 = b2
  · subst h1
    simp only [and_self, if_true, mul_one, if_pos rfl]
    rw [← g68i_purif_smul _ R psi hpurifies a0 c0, g68i_withRef_apply]
    simp [Matrix.smul_apply]
  · simp [h1, Ne.symm h1]

end G68ILIB

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eqs.(21)-(22).
Each conditional purification comes from projection of this same psi.
The printed RHS suppresses id_anc; it is explicitly restored here, as in (23).
The reference and flag are regrouped explicitly on the left. This is a typing
clarification, not an additional communication resource. -/
theorem solution
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    {C : Type*} [Fintype C] [DecidableEq C]
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R)
    (psi : EuclideanSpace ℂ ((Word n d × Word n delta) × C))
    (hpsi : IsState psi) (hpurifies : traceRight (pureDensity psi) = R)
    (a0 : Word n d) (c0 : C) :
    purifiedOutput M n psi = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (withReference (piSuperop (fun _ : Fin n => M))
          (pureDensity (conditionalPurification a0 c0 R psi b)))
        (pureDensity (ket b)) := by
  exact g68i_purif_block d delta n M R psi hpurifies a0 c0



end
