-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.SchurClosable.Main.alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:52:52.636794+00:00
-- url     : https://prove2.me/submissions/084c3476-0705-4732-ab1a-af6208fc91a6

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_HaarTransfer_SchurClosable
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SchurUnitaryInner_UnitaryInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.SchurClosable PI.UnitaryGroupMassFormula.SchurClosable.Main
open Filter Topology
namespace PI.UnitaryGroupMassFormula.SchurClosable.Main
theorem _root_.solution {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] (D : Submodule ℂ H) (A : D →ₗ[ℂ] H') (a : ℂ)
    (hK : ∀ x y : D,
      inner ℂ (x : H) (y : H) = a * (inner ℂ (x : H) (y : H) + inner ℂ (A x) (A y))) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ x y : D, inner ℂ (A x) (A y) = (c : ℂ) * inner ℂ (x : H) (y : H) := by
  by_cases h : ∃ x : D, (x : H) ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h
    have hn : 0 < ‖(x₀ : H)‖ := norm_pos_iff.mpr hx₀
    have hs : 0 < ‖(x₀ : H)‖ ^ 2 := pow_pos hn 2
    have ht : 0 ≤ ‖A x₀‖ ^ 2 := by positivity
    have h0 := hK x₀ x₀
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h0
    refine ⟨‖A x₀‖ ^ 2 / ‖(x₀ : H)‖ ^ 2, div_nonneg ht hs.le, fun x y => ?_⟩
    have hxy := hK x y
    have hsC : ((‖(x₀ : H)‖ : ℂ)) ^ 2 ≠ 0 := by
      have : ((‖(x₀ : H)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs.ne'
      simpa using this
    have key : ((‖(x₀ : H)‖ : ℂ)) ^ 2 * inner ℂ (A x) (A y)
        = ((‖A x₀‖ : ℂ)) ^ 2 * inner ℂ (x : H) (y : H) := by
      linear_combination (inner ℂ (A x) (A y) + inner ℂ (x : H) (y : H)) * h0
        - (((‖(x₀ : H)‖ : ℂ)) ^ 2 + ((‖A x₀‖ : ℂ)) ^ 2) * hxy
    have e1 : ((‖A x₀‖ ^ 2 / ‖(x₀ : H)‖ ^ 2 : ℝ) : ℂ)
        = ((‖A x₀‖ : ℂ)) ^ 2 / ((‖(x₀ : H)‖ : ℂ)) ^ 2 := by push_cast; ring
    rw [e1, div_mul_eq_mul_div, eq_div_iff hsC]
    linear_combination key
  · simp only [not_exists, not_not] at h
    refine ⟨0, le_rfl, fun x y => ?_⟩
    have hx : x = 0 := Subtype.ext (h x)
    simp [hx]
end PI.UnitaryGroupMassFormula.SchurClosable.Main
