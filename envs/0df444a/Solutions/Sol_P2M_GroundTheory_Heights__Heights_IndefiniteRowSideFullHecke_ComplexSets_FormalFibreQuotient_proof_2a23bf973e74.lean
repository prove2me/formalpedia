-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FormalFibreQuotient_proof_2a23bf973e74
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:58:40.381636+00:00
-- url     : https://prove2.me/submissions/3d922f0c-f322-406a-89a3-f419f72e7c90

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFormalFibreQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFormalFibreQuotient
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_primeFibreLocalRing_nonempty_equiv_of_surjective_56cf03546f44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_exists_adicCompletion_surjection_of_surjective_bd96116c27fb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace FormalFibreQuotient
theorem _root_.solution : FormalFibreQuotient.Statement := by
  intro B A _ _ f hf hB m P _
  obtain ⟨φ, hφ, hcomm, hker⟩ := exists_adicCompletion_surjection_of_surjective f hf hB m
  refine ⟨⟨P.comap φ, inferInstance⟩, ?_, ?_⟩
  · change (P.comap φ).comap _ = _
    rw [Ideal.comap_comap, hcomm, ← Ideal.comap_comap]
  · exact primeFibreLocalRing_nonempty_equiv_of_surjective f φ hf hφ hcomm hker P
end FormalFibreQuotient
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
