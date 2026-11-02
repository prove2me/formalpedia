-- Prove2me | solution 1 for OblivEllipsoid.Infeas.proposition_7_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T08:29:14.516797+00:00
-- url     : https://prove2.me/submissions/573f4c46-3486-41f6-9ed1-1caa8d4b204d

import Mathlib
import Definitions.Def_OblivEllipsoid_Infeas_Model

open Matrix

namespace OblivEllipsoid.Infeas
namespace OEAProp71

lemma AT_mulVec_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin n → ℝ) (k : Fin m) :
    (Aᵀ *ᵥ x) k = col A k ⬝ᵥ x := by
  simp [Matrix.mulVec, dotProduct, col, Matrix.transpose_apply]

lemma quad_B {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) (x : Fin n → ℝ) :
    x ⬝ᵥ (B A d *ᵥ x) = ∑ k : Fin m, d k * (col A k ⬝ᵥ x) ^ 2 := by
  have h1 : B A d *ᵥ x = A *ᵥ (diagonal d *ᵥ (Aᵀ *ᵥ x)) := by
    simp [B, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.mulVec_diagonal, AT_mulVec_apply]
  refine Finset.sum_congr rfl fun k _ => by ring

lemma B_symm {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (d : Fin m → ℝ) :
    (B A d)ᵀ = B A d := by
  simp [B, Matrix.transpose_mul, Matrix.mul_assoc]

/-- Under Assumption 1.1 and `d > 0`, `B(d)` is invertible. -/
lemma B_isUnit {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) (hA : Assumption11 A)
    (d : Fin m → ℝ) (hd : ∀ i, 0 < d i) : IsUnit (B A d) := by
  rw [← Matrix.mulVec_injective_iff_isUnit]
  suffices H : ∀ x, B A d *ᵥ x = 0 → x = 0 by
    intro x y hxy
    have := H (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
    exact sub_eq_zero.1 this
  intro x hx
  have hq : ∑ k : Fin m, d k * (col A k ⬝ᵥ x) ^ 2 = 0 := by
    rw [← quad_B, hx, dotProduct_zero]
  have hall : ∀ k, col A k ⬝ᵥ x = 0 := by
    intro k
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => by
      have := hd k; positivity)).1 hq k (Finset.mem_univ _)
    have hdk := (hd k).ne'
    have : (col A k ⬝ᵥ x) ^ 2 = 0 := by
      rcases mul_eq_zero.1 this with h | h
      · exact absurd h hdk
      · exact h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  obtain ⟨lam, -, hlam⟩ := hA.1 x
  have hATx : Aᵀ *ᵥ x = 0 := by
    funext k; rw [AT_mulVec_apply]; exact hall k
  have : x ⬝ᵥ x = 0 := by
    calc x ⬝ᵥ x = x ⬝ᵥ (A *ᵥ lam) := by rw [hlam]
      _ = 0 := by
        rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hATx, zero_dotProduct]
  exact dotProduct_self_eq_zero.1 this

theorem prop71 {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hf : 0 < f A u d ell) :
    ∀ i : Fin m, slabRadius A u d ell i ≤
      (d i / f A u d ell) ^ (-(1 / 2 : ℝ)) := by
  intro i
  set w := (B A d)⁻¹ *ᵥ col A i with hw
  have hBu := B_isUnit A hA d hd
  have hBw : B A d *ᵥ w = col A i := by
    rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hBu),
      Matrix.one_mulVec]
  set q := col A i ⬝ᵥ w with hq
  have hq_eq : q = ∑ k : Fin m, d k * (col A k ⬝ᵥ w) ^ 2 := by
    rw [← quad_B, hBw, hq, dotProduct_comm]
  have hq_nonneg : 0 ≤ q := by
    rw [hq_eq]; exact Finset.sum_nonneg fun k _ => by have := hd k; positivity
  have hq_ge : d i * q ^ 2 ≤ q := by
    have := Finset.single_le_sum (f := fun k => d k * (col A k ⬝ᵥ w) ^ 2)
      (fun k _ => by have := hd k; positivity) (Finset.mem_univ i)
    simpa [← hq_eq] using this
  have hdi := hd i
  have hq_le : q ≤ 1 / d i := by
    rcases hq_nonneg.eq_or_lt with h | h
    · rw [← h]; positivity
    · rw [le_div_iff₀ hdi]
      nlinarith
  have hS : slabRadius A u d ell i = Real.sqrt (f A u d ell * q) := rfl
  have hR : (d i / f A u d ell) ^ (-(1 / 2 : ℝ)) = Real.sqrt (f A u d ell / d i) := by
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow, ← Real.sqrt_inv, inv_div]
  rw [hS, hR]
  apply Real.sqrt_le_sqrt
  calc f A u d ell * q ≤ f A u d ell * (1 / d i) := by gcongr
    _ = f A u d ell / d i := by ring

end OEAProp71
end OblivEllipsoid.Infeas

open OblivEllipsoid.Infeas in
theorem solution {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (u d ell : Fin m → ℝ) (hA : Assumption11 A)
    (hd : ∀ i, 0 < d i) (hf : 0 < f A u d ell) :
    ∀ i : Fin m, slabRadius A u d ell i ≤
      (d i / f A u d ell) ^ (-(1 / 2 : ℝ)) :=
  OblivEllipsoid.Infeas.OEAProp71.prop71 A u d ell hA hd hf
