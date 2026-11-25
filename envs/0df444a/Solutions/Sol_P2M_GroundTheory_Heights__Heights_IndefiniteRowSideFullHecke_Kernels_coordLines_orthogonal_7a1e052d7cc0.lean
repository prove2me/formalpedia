-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_orthogonal_7a1e052d7cc0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:06:11.537221+00:00
-- url     : https://prove2.me/submissions/ffb8aa46-0e71-4c81-af85-1b4d5c6960d1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_standard_inner_single_ne_650d14c0e8b4

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
theorem _root_.solution (K : Type*) [Field K] [NumberField K] :
    IsOrthogonalFamily (HermitianBundle.standard K 2) (coordLines K) := by
  intro σ x y hxy l hl l' hl'
  obtain ⟨a, rfl⟩ := hl
  obtain ⟨b, rfl⟩ := hl'
  exact standard_inner_single_ne K σ x y hxy a b
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
