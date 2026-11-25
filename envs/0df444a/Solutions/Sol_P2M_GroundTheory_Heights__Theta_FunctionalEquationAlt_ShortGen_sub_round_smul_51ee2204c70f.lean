-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_sub_round_smul_51ee2204c70f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:06:22.337122+00:00
-- url     : https://prove2.me/submissions/43b6a402-cbb5-4b52-847d-022d3ad16d72

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_apply_bc8e45da2f5a

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
theorem _root_.solution (v x : W) :
    x - (round (inner ℝ v x / ‖v‖ ^ 2)) • v =
      proj v x + (inner ℝ v x / ‖v‖ ^ 2 - round (inner ℝ v x / ‖v‖ ^ 2)) • v := by
  rw [proj_apply, sub_smul, ← Int.cast_smul_eq_zsmul ℝ]
  abel
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
