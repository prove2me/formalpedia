-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_rename_pairCollapse_idem_785cf95a1311
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:40:41.192743+00:00
-- url     : https://prove2.me/submissions/c61c2f2d-6a1b-45a8-a65e-f83b7fcfe718

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OfSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberExpansionKoszul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_pairCollapse_comp_e391be9b6313

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (p : Fin n) (G : MvPolynomial (Fin n ⊕ Fin n) ℤ) :
    rename (pairCollapse p) (rename (pairCollapse p) G) = rename (pairCollapse p) G := by
  rw [rename_rename, pairCollapse_comp]
end GroundTheory.Heights₂.Heights.NumbersDVR
