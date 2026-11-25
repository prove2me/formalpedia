-- Prove2me | solution 1 for P2M_PI_Witt_anisotropic__ba4aff8f3cd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:50:23.829627+00:00
-- url     : https://prove2.me/submissions/e3c3a98a-c645-46df-a597-d146b4fb5b9c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_Anisotropic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WittDecomposition_AnisotropicHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Witt
namespace PI.Witt
theorem _root_.solution : Anisotropic := by
  unfold Anisotropic
  intro K V _ _ _ _ _ B hB U hU
  obtain ⟨x, hx, y, hy, hxy⟩ := hU
  by_contra hcon
  push_neg at hcon
  have hz : x + star (B x y) • y ∈ U := U.add_mem hx (U.smul_mem _ hy)
  have h0 := hcon _ hz
  have hxx := hcon x hx
  have hyy := hcon _ (U.smul_mem (star (B x y)) hy)
  have hyx : B y x = star (B x y) := (hB x y).symm
  have e1 : B x (star (B x y) • y) = star (B x y) * B x y := by
    rw [LinearMap.map_smul, smul_eq_mul]
  have e2 : B (star (B x y) • y) x = B x y * star (B x y) := by
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star, hyx]
  have e3 : B (x + star (B x y) • y) (x + star (B x y) • y) =
      B x x + B x (star (B x y) • y) + (B (star (B x y) • y) x + B (star (B x y) • y) (star (B x y) • y)) := by
    rw [LinearMap.map_add₂, map_add, map_add]
  rw [e3, hxx, hyy, e1, e2] at h0
  have h2 : (2 : K) * (B x y * star (B x y)) = 0 := by linear_combination h0
  rcases mul_eq_zero.mp h2 with h | h
  · exact two_ne_zero h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact hxy h'
    · exact hxy (star_eq_zero.mp h')
end PI.Witt
