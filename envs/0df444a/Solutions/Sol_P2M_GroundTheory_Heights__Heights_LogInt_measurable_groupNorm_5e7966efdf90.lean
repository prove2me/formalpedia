-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LogInt_measurable_groupNorm_5e7966efdf90
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:09:14.103554+00:00
-- url     : https://prove2.me/submissions/d74f2d21-d0ba-4456-a1bd-3487598c073d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntPoly
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LogIntSphere
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermNorm_li_continuous_norm_4f6d1b6879e1

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
open MeasureTheory Set MvPolynomial Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.LogInt
variable {n k : ℕ}
namespace GroundTheory.Heights₂.Heights.LogInt
theorem _root_.solution (h : HermNorm n) (i : Fin k) :
    Measurable fun u : Fin k × Fin n → ℂ => h.norm fun j => u (i, j) :=
  h.li_continuous_norm.measurable.comp (measurable_pi_lambda _ fun _ => measurable_pi_apply _)
end GroundTheory.Heights₂.Heights.LogInt
