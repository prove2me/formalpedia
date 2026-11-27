-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_S6_LineCoordinates_hypotheses_inhabited_1c32a85e413a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:58:40.353645+00:00
-- url     : https://prove2.me/submissions/37d587c4-66e3-4c71-a491-8ca961bdf936

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KernelsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StandardInnerSingleNe
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_AssemblyLines
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StdCoordMapInjective
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_isInternal_a6f5bd44f003
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_orthogonal_7a1e052d7cc0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Kernels_coordLines_rank_8d1ca699d468


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
open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
noncomputable section
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
namespace S6.LineCoordinates
theorem _root_.solution :
    DirectSum.IsInternal (coordLines ℚ) ∧
      (∀ x, (HermitianBundle.standard ℚ 2).rank (coordLines ℚ x) = 1) ∧
      IsOrthogonalFamily (HermitianBundle.standard ℚ 2) (coordLines ℚ) :=
  ⟨coordLines_isInternal ℚ, coordLines_rank ℚ, coordLines_orthogonal ℚ⟩
end S6.LineCoordinates
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
