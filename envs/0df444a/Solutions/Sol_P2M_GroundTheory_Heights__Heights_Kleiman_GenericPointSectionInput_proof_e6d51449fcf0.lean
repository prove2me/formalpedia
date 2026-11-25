-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_GenericPointSectionInput_proof_e6d51449fcf0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:33:57.55542+00:00
-- url     : https://prove2.me/submissions/87ae7f47-d88c-4f48-8847-a9cd2bada31a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumEventual
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumAdditive
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumCut
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_StInterNumPointDeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_InterSumEventuallyEqInterNum
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interNum_comp_perm_080c53d7c885
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_interSum_eventually_eq_interNum_03856f55128c

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial Filter
noncomputable section
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace GenericPointSectionInput
theorem _root_.solution (hE : InterNumEventual.Statement.{u, w})
    (hA : InterNumAdditive.Statement.{u, w}) (hC : InterNumCut.Statement.{u, w})
    (hP : InterNumPointDeg.Statement.{u, w}) : GenericPointSectionInput.Statement.{u, w} := by
  intro k _ Ω _ _ N x
  refine ⟨fun n pp L hW => ?_, fun n pp L σ _ => ?_, fun n pp L i L' L'' hW => ?_,
    fun n pp L Lc s hW hs hne => ?_, fun pp hW => ?_⟩
  · obtain ⟨m, hm⟩ := hE k Ω N x n pp L hW
    exact interSum_eventually_eq_interNum pp _ hm
  · exact interNum_comp_perm pp (fun i => (L i).toSubSystem) σ
  · exact hA k Ω N x n pp L i L' L'' hW
  · exact hC k Ω N x n pp L Lc s hW hs hne
  · exact hP k Ω N x pp hW
end GenericPointSectionInput
end GroundTheory.Heights₂.Heights.Kleiman
