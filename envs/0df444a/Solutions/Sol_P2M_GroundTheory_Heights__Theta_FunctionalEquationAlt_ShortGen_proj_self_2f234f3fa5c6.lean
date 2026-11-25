-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:57:36.495018+00:00
-- url     : https://prove2.me/submissions/400f4b25-c2a3-41a8-93f3-22ddebb45659

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_smul_self_7b304758589a

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt
open GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
open Module Submodule Matrix
open scoped RealInnerProductSpace
noncomputable section
variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
omit [FiniteDimensional ℝ W]
namespace GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
theorem _root_.solution (v : W) (hv : v ≠ 0) : proj v v = 0 := by
  simpa using proj_smul_self v 1 hv
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
