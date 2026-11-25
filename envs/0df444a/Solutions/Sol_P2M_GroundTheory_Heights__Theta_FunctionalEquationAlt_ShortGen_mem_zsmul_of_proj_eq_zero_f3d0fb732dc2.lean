-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_FunctionalEquationAlt_ShortGen_mem_zsmul_of_proj_eq_zero_f3d0fb732dc2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:19:29.297658+00:00
-- url     : https://prove2.me/submissions/5c0b37ea-8b8b-48f4-88c3-5fa01f44d877

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_CovolumeCount
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_LinearIndependentRealOfInt
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
    (hmin : ∀ x ∈ L, x ≠ 0 → ‖v‖ ≤ ‖x‖) {y : W} (hy : y ∈ L) (h0 : proj v y = 0) :
    ∃ k : ℤ, y = k • v := by
  refine ⟨round (inner ℝ v y / ‖v‖ ^ 2), ?_⟩
  have hd := sub_round_smul v y
  rw [h0, zero_add] at hd
  by_contra hne
  have hmem : y - round (inner ℝ v y / ‖v‖ ^ 2) • v ∈ L := L.sub_mem hy (L.smul_mem _ hvL)
  have h1 := hmin _ hmem (sub_ne_zero.2 hne)
  rw [hd, norm_smul, Real.norm_eq_abs] at h1
  have hs := abs_sub_round (inner ℝ v y / ‖v‖ ^ 2)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv
  nlinarith
end GroundTheory.Heights₂.Theta.FunctionalEquationAlt.ShortGen
