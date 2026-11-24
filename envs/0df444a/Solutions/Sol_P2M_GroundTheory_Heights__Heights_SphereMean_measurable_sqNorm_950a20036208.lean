-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SphereMean_measurable_sqNorm_950a20036208
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:44.355027+00:00
-- url     : https://prove2.me/submissions/45002d08-5cae-432c-87b5-ec84711891f5

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
theorem _root_.solution (n : ℕ) : Measurable (sqNorm (n := n)) :=
  (continuous_sqNorm n).measurable
end GroundTheory.Heights₂.Heights.SphereMean
