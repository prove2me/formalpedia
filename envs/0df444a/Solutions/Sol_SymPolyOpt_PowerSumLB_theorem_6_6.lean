-- Prove2me | solution 1 for SymPolyOpt.PowerSumLB.theorem_6_6
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T20:40:41.292303+00:00
-- url     : https://prove2.me/submissions/be85faea-adad-4f66-b8e9-dfd3eb45aec2

import Mathlib
import Definitions.Def_SymPolyOpt_PowerSumLB_Setting
open Matrix

namespace RRAux_SymPolyOpt_PowerSumLB_theorem_6_6

open SymPolyOpt.PowerSumLB

def V {n : ℕ} (k : ℕ) (x : Fin n → ℝ) : Matrix (Fin n) (Fin k) ℝ := Matrix.of fun a i => x a ^ (i : ℕ)

lemma hankel_eq {n : ℕ} (k : ℕ) (x : Fin n → ℝ) :
    hankel k (powerSum x) = (V k x)ᵀ * V k x := by
  ext i j
  simp [hankel, powerSum, V, Matrix.mul_apply, pow_add]

lemma hankel_psd {n : ℕ} (x : Fin n → ℝ) : (hankel n (powerSum x)).PosSemidef := by
  rw [hankel_eq]
  have := posSemidef_conjTranspose_mul_self (V n x)
  rwa [conjTranspose_eq_transpose_of_trivial] at this

lemma key {n : ℕ} (r : ℕ) (x : Fin n → ℝ) (H : Matrix (Fin r) (Fin r) ℝ)
    (hH : H = (V r x)ᵀ * V r x) (hu : IsUnit H.det) (u : Fin r → ℝ)
    (hu' : u = (V r x)ᵀ *ᵥ (fun a => x a ^ r)) :
    u ⬝ᵥ (H⁻¹ *ᵥ u) ≤ powerSum x (2 * r) := by
  set w : Fin n → ℝ := fun a => x a ^ r with hw
  set c := H⁻¹ *ᵥ u with hc
  have h0 : 0 ≤ (w - V r x *ᵥ c) ⬝ᵥ (w - V r x *ᵥ c) := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have h1 : w ⬝ᵥ (V r x *ᵥ c) = u ⬝ᵥ c := by
    rw [dotProduct_mulVec, hu', mulVec_transpose]
  have h2 : (V r x *ᵥ c) ⬝ᵥ (V r x *ᵥ c) = u ⬝ᵥ c := by
    rw [dotProduct_mulVec, ← mulVec_transpose, mulVec_mulVec, ← hH, hc, mulVec_mulVec,
      mul_nonsing_inv _ hu, one_mulVec]
  have h3 : w ⬝ᵥ w = powerSum x (2 * r) := by
    simp [hw, dotProduct, powerSum, pow_mul', sq]
  have h4 : (w - V r x *ᵥ c) ⬝ᵥ (w - V r x *ᵥ c) =
      w ⬝ᵥ w - 2 * (w ⬝ᵥ (V r x *ᵥ c)) + (V r x *ᵥ c) ⬝ᵥ (V r x *ᵥ c) := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm (V r x *ᵥ c) w]
    ring
  rw [h4, h1, h2, h3] at h0
  linarith

end RRAux_SymPolyOpt_PowerSumLB_theorem_6_6

open RRAux_SymPolyOpt_PowerSumLB_theorem_6_6 in
open SymPolyOpt.PowerSumLB in
theorem solution (n m q : ℕ) (γ : ℕ → ℝ) (hm : m ≤ n + 1) (hmq : m ≤ q) (hq : q ≤ 2 * n - 2) :
    valL n m q γ ≤ minP n m q γ ∧
    ∀ r : ℕ, q = 2 * r → m = 2 * r → (hankel r (gammaExt n γ)).PosDef →
      (((fun i : Fin r => γ (r + i)) ⬝ᵥ
          ((hankel r (gammaExt n γ))⁻¹ *ᵥ fun i : Fin r => γ (r + i)) : ℝ) : EReal)
        ≤ minP n m q γ := by
  refine ⟨?_, ?_⟩
  · refine le_iInf₂ fun x hx => ?_
    refine iInf₂_le_of_le (powerSum x) ⟨hankel_psd x, by simp [powerSum], hx⟩ le_rfl
  · intro r hqr hmr hH
    refine le_iInf₂ fun x hx => ?_
    rw [hqr]
    refine EReal.coe_le_coe_iff.mpr ?_
    have hHeq : hankel r (gammaExt n γ) = (V r x)ᵀ * V r x := by
      rw [← hankel_eq]
      ext i j
      simp only [hankel, gammaExt]
      split_ifs with h
      · rw [h]; simp [powerSum]
      · have hi := i.2; have hj := j.2
        exact (hx _ (by omega) (by omega)).symm
    refine key r x _ hHeq ((isUnit_iff_isUnit_det _).mp hH.isUnit) _ ?_
    ext i
    have hi := i.2
    rw [hx _ (by omega) (by omega) |>.symm]
    simp [V, mulVec, dotProduct, powerSum, pow_add, mul_comm]

#print axioms solution
