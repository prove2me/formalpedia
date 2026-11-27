-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_factors_8dc1eaffddb3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:11:33.358908+00:00
-- url     : https://prove2.me/submissions/8827a84f-1c62-4332-a2d0-19c4b281b291

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_LieCoordinates_SecondKindStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Theta_EisensteinZeta_MirabolicInduction_HsInnerSelfEqSumSq
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_E_apply_of_ne_3d49cd00040c
import Theorems.Thm_P2M_GroundTheory_Heights__Theta_SecondKind_UnitaryRecombination_card_place_2ef5794d3fc9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Theta
open Matrix GroundTheory.Automorphic
open scoped Matrix.Norms.L2Operator
noncomputable section
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Theta.SecondKind
open GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
namespace GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
theorem _root_.solution : Factors.Statement := by
  intro F
  refine ⟨fun k l hkl s t => ?_, fun τ => card_place F τ⟩
  have h0 : (s • F.E k) * (t • F.E l) = 0 := by
    funext τ
    by_cases hk : τ = F.place k
    · have : τ ≠ F.place l := fun h => hkl (hk.symm.trans h)
      simp [Pi.mul_apply, E_apply_of_ne F this]
    · simp [Pi.mul_apply, E_apply_of_ne F hk]
  have h1 : (t • F.E l) * (s • F.E k) = 0 := by
    funext τ
    by_cases hk : τ = F.place k
    · have : τ ≠ F.place l := fun h => hkl (hk.symm.trans h)
      simp [Pi.mul_apply, E_apply_of_ne F this]
    · simp [Pi.mul_apply, E_apply_of_ne F hk]
  have hc : Commute (s • F.E k) (t • F.E l) := h0.trans h1.symm
  exact hc.exp.eq
end GroundTheory.Heights₂.Theta.SecondKind.UnitaryRecombination
