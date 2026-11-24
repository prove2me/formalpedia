-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_isOpen_ballSet_4b2e1ed44a1c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:42:53.657449+00:00
-- url     : https://prove2.me/submissions/676d1c6e-da00-44c7-b167-cb983ae88a81

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMeanVol
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_SphereMean_continuous_sqNorm_309bdd8d6577

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
theorem _root_.solution (n : ℕ) (s : ℝ) : IsOpen (ballSet n s) :=
  isOpen_lt (continuous_sqNorm n) continuous_const
end GroundTheory.Heights₂.Heights.SphereMean
