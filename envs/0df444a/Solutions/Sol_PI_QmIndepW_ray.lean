-- Prove2me | solution 1 for PI.QmIndepW.ray
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:12:47.684731+00:00
-- url     : https://prove2.me/submissions/055c963c-8e37-428c-8102-3895d69d7d0c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuarticIndependence_IndepC
import Theorems.Thm_PI_QmIndepW_quartic_coeffs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.QmIndepW
open Complex
namespace PI.QmIndepW
theorem _root_.solution (y00 y10 y20 y01 y11 y21 y02 y12 y22 : ℂ)
    (hyp : ∀ c : ℂ, c ≠ 0 → nine c⁻¹ (star c)⁻¹ y00 y10 y20 y01 y11 y21 y02 y12 y22 = 0)
    (ω ω' : ℂ) (hω : ω ≠ 0) (hs : star ω = ω') :
    y00 = 0 ∧ ω * y10 + ω' * y01 = 0 ∧ ω ^ 2 * y20 + ω * ω' * y11 + ω' ^ 2 * y02 = 0 ∧
      ω ^ 2 * ω' * y21 + ω * ω' ^ 2 * y12 = 0 ∧ ω ^ 2 * ω' ^ 2 * y22 = 0 := by
  refine quartic_coeffs _ _ _ _ _ fun t ht1 _ => ?_
  have ht : (t : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h := hyp _ (inv_ne_zero (mul_ne_zero ht hω))
  simp only [inv_inv, star_inv₀, star_mul', star_natCast, hs, nine] at h
  linear_combination h
end PI.QmIndepW
