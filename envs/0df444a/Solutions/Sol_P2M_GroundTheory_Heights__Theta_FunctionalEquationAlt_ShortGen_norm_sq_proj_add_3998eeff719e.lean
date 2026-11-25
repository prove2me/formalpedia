-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_norm_sq_proj_add_3998eeff719e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:41:40.451809+00:00
-- url     : https://prove2.me/submissions/f77e0a2b-66ec-47bf-8d9b-fdbbeb1b3b63

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_inner_proj_6ef07283d6e8

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
theorem _root_.solution (v x : W) (hv : v ≠ 0) (s : ℝ) :
    ‖proj v x + s • v‖ ^ 2 = ‖proj v x‖ ^ 2 + s ^ 2 * ‖v‖ ^ 2 := by
  rw [norm_add_sq_real, real_inner_smul_right, real_inner_comm, inner_proj v x hv, norm_smul,
    Real.norm_eq_abs, mul_pow, sq_abs]
  ring
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
