-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_exists_lift_4f41a057c0ff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:22.340132+00:00
-- url     : https://prove2.me/submissions/d81ca1b0-f3ba-45e3-93e4-3246b233ec7a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_sub_round_smul_51ee2204c70f

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
theorem _root_.solution {L : Submodule ℤ W} {v : W} (hvL : v ∈ L) (hv : v ≠ 0) {x : W} (hx : x ∈ L) :
    ∃ y ∈ L, proj v y = proj v x ∧ ‖y‖ ≤ ‖proj v x‖ + ‖v‖ / 2 := by
  refine ⟨x - round (inner ℝ v x / ‖v‖ ^ 2) • v, L.sub_mem hx (L.smul_mem _ hvL), ?_, ?_⟩
  · rw [map_sub, map_zsmul, proj_self v hv, smul_zero, sub_zero]
  · rw [sub_round_smul]
    have h1 := norm_add_le (proj v x)
      ((inner ℝ v x / ‖v‖ ^ 2 - round (inner ℝ v x / ‖v‖ ^ 2)) • v)
    have h2 : ‖(inner ℝ v x / ‖v‖ ^ 2 - round (inner ℝ v x / ‖v‖ ^ 2)) • v‖ ≤ ‖v‖ / 2 := by
      rw [norm_smul, Real.norm_eq_abs]
      have := abs_sub_round (inner ℝ v x / ‖v‖ ^ 2)
      nlinarith [norm_nonneg v]
    linarith
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
