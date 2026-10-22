-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P38.dephasedOutput_blockDecomposition
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:29:45.059708+00:00
-- url     : https://prove2.me/submissions/762786df-c72e-40bc-ab43-9302cd8ae934

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

end G68ILIB

/-- Giovannetti, arXiv:quant-ph/0406111v3, PDF p.4, Eqs.(17)-(18).
Every conditional input and weight is computed from R. No conditional block
or output decomposition is a hypothesis. The arbitrary a0 only selects a
normalized state on zero-probability branches. -/
theorem solution
    (d delta n : ℕ) (hd : 2 ≤ d) (hdelta : 0 < delta) (hn : 0 < n)
    (M : Superop (Fin d) (Fin d)) (hM : IsChannel M)
    (R : Matrix (Word n d × Word n delta) (Word n d × Word n delta) ℂ)
    (hR : IsDensityMatrix R) (a0 : Word n d) :
    dephasedPower M n R = ∑ b : Word n delta,
      (branchWeight R b : ℂ) • Matrix.kronecker
        (piSuperop (fun _ : Fin n => M) (conditionalState a0 R b))
        (pureDensity (ket b)) := by
  exact g68i_deph_block d delta n M R hR a0



end
