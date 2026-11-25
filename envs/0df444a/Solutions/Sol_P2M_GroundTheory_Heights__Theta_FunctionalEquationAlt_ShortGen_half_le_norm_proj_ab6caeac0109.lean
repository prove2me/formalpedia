-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_half_le_norm_proj_ab6caeac0109
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:18:27.571852+00:00
-- url     : https://prove2.me/submissions/cbfac339-3ebe-4f6f-b7e4-cba2c2ad2010

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_proj_self_2f234f3fa5c6
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_norm_sq_proj_add_3998eeff719e
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
theorem _root_.solution {L : Submodule ℤ W} {v : W} (hvL : v ∈ L) (hv : v ≠ 0)
    (hmin : ∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖x‖) {x : W} (hx : x ∈ L) (h0 : proj v x ≠ 0) :
    ‖v‖ / 2 ≤ ‖proj v x‖ := by
  have hd := sub_round_smul v x
  have hmem : x - round (inner ℝ v x / ‖v‖ ^ 2) • v ∈ L := L.sub_mem hx (L.smul_mem _ hvL)
  have hne : x - round (inner ℝ v x / ‖v‖ ^ 2) • v ≠ 0 := by
    intro h
    apply h0
    rw [sub_eq_zero.1 h, map_zsmul, proj_self v hv, smul_zero]
  have h1 := hmin _ hmem hne
  rw [hd] at h1
  have h2 := norm_sq_proj_add v x hv (inner ℝ v x / ‖v‖ ^ 2 - round (inner ℝ v x / ‖v‖ ^ 2))
  have hs := abs_sub_round (inner ℝ v x / ‖v‖ ^ 2)
  have hs2 : (inner ℝ v x / ‖v‖ ^ 2 - round (inner ℝ v x / ‖v‖ ^ 2)) ^ 2 ≤ 1 / 4 := by
    have := abs_nonneg (inner ℝ v x / ‖v‖ ^ 2 - round (inner ℝ v x / ‖v‖ ^ 2))
    rw [← sq_abs]
    nlinarith
  have h3 : ‖v‖ ^ 2 ≤ ‖proj v x‖ ^ 2 + ‖v‖ ^ 2 / 4 := by
    have := pow_le_pow_left₀ (norm_nonneg v) h1 2
    nlinarith [sq_nonneg ‖v‖]
  by_contra hlt
  have hlt' := lt_of_not_ge hlt
  nlinarith [norm_nonneg (proj v x), sq_nonneg ‖v‖]
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
