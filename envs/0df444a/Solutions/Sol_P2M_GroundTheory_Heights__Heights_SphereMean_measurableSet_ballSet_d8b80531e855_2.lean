-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_SphereMean_measurableSet_ballSet_d8b80531e855
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:49:41.240424+00:00
-- url     : https://prove2.me/submissions/cdaae14f-a5f9-47e9-9d68-229f09c917a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_isOpen_ballSet_4b2e1ed44a1c

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
namespace GroundTheory.Heights₂.Heights.SphereMean
theorem _root_.solution (n : ℕ) (s : ℝ) : MeasurableSet (ballSet n s) :=
  (isOpen_ballSet n s).measurableSet
end GroundTheory.Heights₂.Heights.SphereMean
