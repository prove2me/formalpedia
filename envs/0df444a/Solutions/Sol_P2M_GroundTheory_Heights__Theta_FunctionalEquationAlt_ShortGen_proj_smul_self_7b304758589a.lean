-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_smul_self_7b304758589a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:42:32.040146+00:00
-- url     : https://prove2.me/submissions/f0678a04-a493-46bb-b7c8-f0edddeb20d4

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
theorem _root_.solution (v : W) (t : ℝ) (hv : v ≠ 0) : proj v (t • v) = 0 := by
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hv)
  rw [proj_apply, real_inner_smul_right, real_inner_self_eq_norm_sq, mul_div_assoc, div_self hn,
    mul_one, sub_self]
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
