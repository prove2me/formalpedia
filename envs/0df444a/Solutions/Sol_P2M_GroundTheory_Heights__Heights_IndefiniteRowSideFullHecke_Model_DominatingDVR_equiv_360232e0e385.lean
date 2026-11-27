-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_DominatingDVR_equiv_360232e0e385
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:59:36.770949+00:00
-- url     : https://prove2.me/submissions/37e00e10-c43b-48c6-84db-6831f664b0f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_IsIsoPullbackObjUnitToUnit
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Imports
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Model_Dominates_equiv_25ce9aaa0a49

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
namespace DominatingDVR
theorem _root_.solution :
    (GroundTheory.Heights₂.Heights.Model.DominatingDVR.Statement ∧
        GroundTheory.Heights₂.Heights.Model.DominatingDVRScheme.Statement) ↔
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model.DominatingDVR.Statement := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun A K _ _ _ _ _ _ _ hA => ?_, fun Z _ _ z hz => ?_⟩
    · obtain ⟨V, hV, hd⟩ := h1 A hA K
      exact ⟨V, hV, (Dominates.equiv A V).1 hd⟩
    · obtain ⟨V, hV, hd⟩ := h2 Z z hz
      exact ⟨V, hV, (Dominates.equiv _ V).1 hd⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun A _ _ _ _ hA K _ _ _ => ?_, fun Z _ _ z hz => ?_⟩
    · obtain ⟨V, hV, hd⟩ := h1 A K hA
      exact ⟨V, hV, (Dominates.equiv A V).2 hd⟩
    · obtain ⟨V, hV, hd⟩ := h2 Z z hz
      exact ⟨V, hV, (Dominates.equiv _ V).2 hd⟩
end DominatingDVR
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Model
