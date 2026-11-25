-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_hypotheses_inhabited_687dc14d1232
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:42:29.66283+00:00
-- url     : https://prove2.me/submissions/5cbbe078-93ed-4214-b7cf-257c7b7d2c5f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_isInternal_a6f5bd44f003
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_rank_8d1ca699d468
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_orthogonal_7a1e052d7cc0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
open NumberField TensorProduct GroundTheory.Heights₂.Heights
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6
theorem _root_.solution :
    DirectSum.IsInternal (coordLines ℚ) ∧
      (∀ x, (HermitianBundle.standard ℚ 2).rank (coordLines ℚ x) = 1) ∧
      IsOrthogonalFamily (HermitianBundle.standard ℚ 2) (coordLines ℚ) ∧
      (∀ x, min ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 0))
          ((HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ 1)) ≤
        (HermitianBundle.standard ℚ 2).normDegree (coordLines ℚ x)) ∧
      Nonempty (HermitianExtension (HermitianBundle.integers ℚ) (HermitianBundle.standard ℚ 2)
        (HermitianBundle.integers ℚ)) := by
  refine ⟨coordLines_isInternal ℚ, coordLines_rank ℚ, coordLines_orthogonal ℚ, fun x => ?_,
    ⟨HermitianExtension.standardSplit ℚ⟩⟩
  fin_cases x
  · exact min_le_left _ _
  · exact min_le_right _ _
end S6
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
