-- Prove2me | solution 1 for WheelerDeWittSuperspace.superQuad_pos_of_traceless
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T19:34:03.536482+00:00
-- url     : https://prove2.me/submissions/bcee8694-2a34-4c24-85f7-0456924cb70e

import Mathlib
import Definitions.Def_WheelerDeWittSuperspace

set_option autoImplicit false

open Matrix

open Matrix Kronecker in
theorem WDW4578_kron_pos (m p : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.PosDef) (hp0 : p ≠ 0) :
    0 < ∑ a, ∑ b, ∑ c, ∑ d, m a c * m b d * p a b * p c d := by
  have hK := hm.kronecker hm
  set v : Fin 3 × Fin 3 → ℝ := fun ij => p ij.1 ij.2 with hv
  have hv0 : v ≠ 0 := by
    intro h; apply hp0; ext i j; exact congrFun h (i, j)
  have h1 := hK.dotProduct_mulVec_pos hv0
  have e : star v ⬝ᵥ ((m ⊗ₖ m) *ᵥ v) =
      ∑ a, ∑ b, ∑ c, ∑ d, m a c * m b d * p a b * p c d := by
    simp only [dotProduct, mulVec, star_trivial, Fintype.sum_prod_type, kroneckerMap_apply, hv,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [e] at h1
  exact h1

theorem WDW4578_num (m p : Matrix (Fin 3) (Fin 3) ℝ) (hsym : ∀ i j, p j i = p i j) :
    (∑ a, ∑ b, ∑ c, ∑ d, (m a c * m b d + m a d * m b c - m a b * m c d) * p a b * p c d) =
      2 * (∑ a, ∑ b, ∑ c, ∑ d, m a c * m b d * p a b * p c d) - (∑ a, ∑ b, m a b * p a b) ^ 2 := by
  simp only [Fin.sum_univ_three]
  rw [hsym 0 1, hsym 0 2, hsym 1 2]
  ring

open Matrix WheelerDeWittSuperspace in
theorem solution (m p : Matrix (Fin 3) (Fin 3) ℝ) (hm : m.PosDef)
    (hp : pᵀ = p) (hp0 : p ≠ 0) (htr : (m * p).trace = 0) :
    0 < superQuad m p := by
  have hQ := WDW4578_kron_pos m p hm hp0
  have hV : 0 < volume m := Real.sqrt_pos.mpr hm.det_pos
  have hsym : ∀ i j, p j i = p i j := fun i j => by
    have := congrFun (congrFun hp i) j
    simpa [transpose_apply] using this
  have hT : ∑ a, ∑ b, m a b * p a b = 0 := by
    rw [Matrix.trace] at htr
    simp only [diag, mul_apply] at htr
    rw [← htr]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [hsym]
  have key : superQuad m p =
      (∑ a, ∑ b, ∑ c, ∑ d, (m a c * m b d + m a d * m b c - m a b * m c d) * p a b * p c d) /
        (2 * volume m) := by
    unfold superQuad deWitt
    simp only [Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  rw [key, WDW4578_num m p hsym, hT]
  apply div_pos
  · linarith
  · linarith
