-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T00:32:15.164108+00:00
-- url     : https://prove2.me/submissions/696cdc7a-d2ea-43c4-86c6-a2f7a5416d0d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory Measure Set
open scoped Pointwise
noncomputable section
open GroundTheory.Heights₂.Heights.SphereMean


theorem solution (n : ℕ) (s : ℝ) : MeasurableSet (ballSet n s) := by
  unfold ballSet
  apply measurableSet_lt _ measurable_const
  unfold sqNorm
  fun_prop
