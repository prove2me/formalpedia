-- Prove2me | solution 1 for PI.StabSplit.Alg.unitK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:27:04.066893+00:00
-- url     : https://prove2.me/submissions/7e6314d4-903a-463d-ba3a-5a19eda04b5a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerFlagSplitting_UnitR

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.StabSplit PI.StabSplit.Alg
variable {R : Type*} [Ring R]
variable [StarRing R]
namespace PI.StabSplit.Alg
theorem _root_.solution (H P h : R) (hH : star H = H) (hPH : star P * H = H * P) (hPP : P * P = P)
    (hh : star h * H * h = H) (hU : P * h * (1 - P) = 0) :
    star (h * (1 - P) + P) * H * (h * (1 - P) + P) = H := by
  have r1 : star P * H - H * P = 0 := sub_eq_zero.mpr hPH
  have r2 : P * P - P = 0 := sub_eq_zero.mpr hPP
  have r3 : star h * H * h - H = 0 := sub_eq_zero.mpr hh
  have r5 : (1 - star P) * (star h * star P) = 0 := by
    simpa only [star_mul, star_sub, star_one, star_zero] using congrArg star hU
  have e : star (h * (1 - P) + P) * H * (h * (1 - P) + P) - H =
      H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P := by
    simp only [star_add, star_mul, star_sub, star_one]
    noncomm_ring
  have z : H * (P * P - P) + H * (P * P - P) - (star P * H - H * P) * (1 - P)
      + (1 - star P) * (star h * H * h - H) * (1 - P) + (1 - star P) * (star h * star P) * H
      - (1 - star P) * star h * (star P * H - H * P) + H * (P * h * (1 - P))
      + (star P * H - H * P) * h * (1 - P) + (star P * H - H * P) * P = 0 := by
    simp only [r1, r2, r3, r5, hU, mul_zero, zero_mul, add_zero, sub_zero]
  exact sub_eq_zero.mp (e.trans z)
end PI.StabSplit.Alg
