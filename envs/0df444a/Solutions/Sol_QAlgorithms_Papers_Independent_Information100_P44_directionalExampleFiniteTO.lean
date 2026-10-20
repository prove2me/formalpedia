-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.directionalExampleFiniteTO
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:47:56.446652+00:00
-- url     : https://prove2.me/submissions/ea1f0466-c5c8-407c-82bb-a763b7f3bf3e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

def g52c_sg : Fin 3 → ℂ := ![1, 1, -1]

theorem g52c_sg_sq (i : Fin 3) : g52c_sg i * g52c_sg i = 1 := by
  fin_cases i <;> simp [g52c_sg]

theorem g52c_sign_conj (X : Mat 3) (i j : Fin 3) :
    (signMatrix * X * signMatrixᴴ) i j = g52c_sg i * X i j * g52c_sg j := by
  have hst : star g52c_sg = g52c_sg := by
    funext k; fin_cases k <;> simp [g52c_sg]
  simp only [signMatrix, Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  rw [show (star ![(1 : ℂ), 1, -1]) = g52c_sg from hst]
  rfl

theorem g52c_dm_apply (q : ℝ) (X : Mat 3) (i j : Fin 3) :
    directionalMixture q X i j = ((q : ℂ) + ((1 - q : ℝ) : ℂ) * (g52c_sg i * g52c_sg j)) * X i j := by
  simp only [directionalMixture, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, g52c_sign_conj]
  ring


def g52c_ctrl (q : ℝ) (m : Fin 2) : Prop := (1/2 ≤ q ∧ m = 0) ∨ (q < 1/2 ∧ m = 1)

def g52c_tau (q : ℝ) (m : Fin 2) (r : Fin 3) : ℂ := if g52c_ctrl q m then 1 else g52c_sg r

theorem g52c_U_diag (q : ℝ) :
    mixtureBathUnitary q = Matrix.diagonal (fun x : Fin 3 × Fin 2 => g52c_tau q x.2 x.1) := by
  ext ⟨x1, x2⟩ ⟨y1, y2⟩
  simp only [mixtureBathUnitary, Matrix.diagonal_apply, Prod.mk.injEq]
  by_cases h2 : x2 = y2
  · subst h2
    by_cases h1 : x1 = y1
    · subst h1
      simp only [true_and, if_true]
      unfold g52c_tau g52c_ctrl
      split_ifs <;> simp [signMatrix, Matrix.diagonal_apply, g52c_sg]
    · simp only [h1, and_true, if_true, false_and, if_false]
      split_ifs <;> simp [signMatrix, Matrix.diagonal_apply, Matrix.one_apply, h1]
  · simp [h2]

theorem g52c_unitary (q : ℝ) : mixtureBathUnitary q ∈ Matrix.unitaryGroup (Fin 3 × Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, g52c_U_diag, Matrix.star_eq_conjTranspose,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  rw [← Matrix.diagonal_one]
  congr 1
  funext x
  simp only [Pi.star_apply, g52c_tau]
  split_ifs
  · simp
  · rw [show star (g52c_sg x.1) = g52c_sg x.1 by fin_cases x <;> simp [g52c_sg]]
    exact g52c_sg_sq x.1

theorem g52c_gibbs_bath (beta q : ℝ) (hb : 0 < beta) (hq0 : 0 < q) (hq1 : q < 1) :
    gibbsWeight ![0, mixtureBathGap beta q] beta 0 = (if 1/2 ≤ q then q else 1 - q) ∧
    gibbsWeight ![0, mixtureBathGap beta q] beta 1 = (if 1/2 ≤ q then 1 - q else q) := by
  have hr : ∀ r : ℝ, 0 < r → Real.exp (-beta * (beta⁻¹ * Real.log r)) = r⁻¹ := by
    intro r hr
    have : -beta * (beta⁻¹ * Real.log r) = -Real.log r := by
      rw [← mul_assoc, neg_mul, mul_inv_cancel₀ hb.ne', neg_one_mul]
    rw [this, Real.exp_neg, Real.exp_log hr]
  have h1q : (1 - q) ≠ 0 := by linarith
  have hq0' : q ≠ 0 := hq0.ne'
  simp only [gibbsWeight, mixtureBathGap, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, mul_zero, Real.exp_zero]
  split_ifs with h
  · rw [hr _ (div_pos hq0 (by linarith))]
    constructor <;> (field_simp; try ring)
  · rw [hr _ (div_pos (by linarith) hq0)]
    constructor <;> (field_simp; try ring)

theorem g52c_ite_conj {n : ℕ} (p : Prop) [Decidable p] (A X : Matrix (Fin n) (Fin n) ℂ) :
    (if p then A else 0) * X * (if p then A else 0)ᴴ = if p then A * X * Aᴴ else 0 := by
  split_ifs <;> simp

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution (E0 E1 beta q : ℝ) (hE : E0 ≠ E1)
    (hbeta : 0 < beta) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ D : ThermalDilation ![E0,E1,E1] beta 2,
      D.bathEnergy = ![0, mixtureBathGap beta q] ∧
      (D.U : Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) ℂ) = mixtureBathUnitary q ∧
      ∀ X, thermalApply D X = directionalMixture q X := by
  let D : ThermalDilation ![E0,E1,E1] beta 2 :=
    { bathPositive := by norm_num
      bathEnergy := ![0, mixtureBathGap beta q]
      U := ⟨mixtureBathUnitary q, g52c_unitary q⟩
      support := by
        intro r i nu mu hne
        show mixtureBathUnitary q (r, nu) (i, mu) = 0
        rw [g52c_U_diag, Matrix.diagonal_apply, if_neg]
        intro h
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hne rfl }
  refine ⟨D, rfl, rfl, fun X => ?_⟩
  obtain ⟨hw0, hw1⟩ := g52c_gibbs_bath beta q hbeta hq0 hq1
  have hK : ∀ mu nu : Fin 2, thermalKraus D (mu, nu) =
      if nu = mu then Matrix.diagonal (fun r =>
        (Real.sqrt (gibbsWeight ![0, mixtureBathGap beta q] beta mu) : ℂ) * g52c_tau q mu r) else 0 := by
    intro mu nu
    ext r i
    show (Real.sqrt (gibbsWeight ![0, mixtureBathGap beta q] beta mu) : ℂ) *
      mixtureBathUnitary q (r, nu) (i, mu) = _
    rw [g52c_U_diag, Matrix.diagonal_apply]
    by_cases hnm : nu = mu
    · subst hnm
      by_cases hri : r = i
      · subst hri; simp
      · simp [hri, Matrix.diagonal_apply]
    · simp [hnm]
  ext r s
  simp only [thermalApply, krausApply, Matrix.sum_apply, Fintype.sum_prod_type, hK, g52c_ite_conj]
  simp only [Matrix.ite_apply, Matrix.zero_apply, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true,
    Fin.sum_univ_two]
  simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.diagonal_conjTranspose, Pi.star_apply,
    g52c_dm_apply]
  have hsq : ∀ m : Fin 2, (Real.sqrt (gibbsWeight ![0, mixtureBathGap beta q] beta m) : ℂ) *
      star (Real.sqrt (gibbsWeight ![0, mixtureBathGap beta q] beta m) : ℂ) =
      (gibbsWeight ![0, mixtureBathGap beta q] beta m : ℂ) := by
    intro m
    rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt]
    simp only [gibbsWeight]
    exact div_nonneg (Real.exp_pos _).le (Finset.sum_nonneg (fun i _ => (Real.exp_pos _).le))
  have hst : ∀ r : Fin 3, star (g52c_sg r) = g52c_sg r := by
    intro r; fin_cases r <;> simp [g52c_sg]
  have e0 : ∀ m : Fin 2, ∀ r s' : Fin 3,
      (Real.sqrt (gibbsWeight ![0, mixtureBathGap beta q] beta m) : ℂ) * g52c_tau q m r * X r s' *
        star ((Real.sqrt (gibbsWeight ![0, mixtureBathGap beta q] beta m) : ℂ) * g52c_tau q m s') =
      (gibbsWeight ![0, mixtureBathGap beta q] beta m : ℂ) * (g52c_tau q m r * g52c_tau q m s') * X r s' := by
    intro m r s'
    rw [star_mul', ← hsq m]
    have : star (g52c_tau q m s') = g52c_tau q m s' := by
      unfold g52c_tau; split_ifs
      · simp
      · exact hst s'
    rw [this]; ring
  rw [e0, e0, hw0, hw1]
  have t0 : ∀ r, g52c_tau q 0 r = if 1/2 ≤ q then 1 else g52c_sg r := by
    intro r
    unfold g52c_tau g52c_ctrl
    by_cases hq : 1/2 ≤ q
    · simp [hq]
    · simp [hq]
  have t1 : ∀ r, g52c_tau q 1 r = if 1/2 ≤ q then g52c_sg r else 1 := by
    intro r
    unfold g52c_tau g52c_ctrl
    have f10 : ¬ ((1 : Fin 2) = 0) := by decide
    by_cases hq : (1:ℝ)/2 ≤ q
    · have h1 : ¬ q < 1/2 := not_lt.mpr hq
      simp only [hq, h1, f10, and_false, false_and, or_false, if_false, if_true]
    · have h1 : q < 1/2 := not_le.mp hq
      simp only [hq, h1, false_and, true_and, false_or, eq_self_iff_true, if_true, if_false]
  simp only [t0, t1]
  by_cases hq : 1/2 ≤ q
  · simp only [hq, if_true]
    push_cast; ring
  · simp only [hq, if_false]
    push_cast; ring
