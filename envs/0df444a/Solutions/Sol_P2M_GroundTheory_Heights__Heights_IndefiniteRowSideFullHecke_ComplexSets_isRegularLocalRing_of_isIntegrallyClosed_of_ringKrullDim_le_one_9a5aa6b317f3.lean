-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_isRegularLocalRing_of_isIntegrallyClosed_of_ringKrullDim_le_one_9a5aa6b317f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:31:46.171986+00:00
-- url     : https://prove2.me/submissions/ac19f629-1e2c-41c0-b542-b8deffe80fcc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSerreCriterion
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StNormalLocalDepthTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSerreCriterion

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
open IsLocalRing
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution (B : Type*) [CommRing B] [IsLocalRing B]
    [IsNoetherianRing B] [IsDomain B] [IsIntegrallyClosed B] (h : ringKrullDim B ≤ 1) : IsRegularLocalRing B := by
  by_cases hf : IsField B
  · let := hf.toField
    infer_instance
  · have : Ring.KrullDimLE 1 B := Ring.krullDimLE_iff.mpr (by exact_mod_cast h)
    have hm : maximalIdeal B ≠ ⊥ := fun hm => hf (isField_iff_maximalIdeal_eq.mpr hm)
    have h3 : IsIntegrallyClosed B ∧ ∃! P : Ideal B, P ≠ ⊥ ∧ P.IsPrime :=
      ⟨inferInstance, maximalIdeal B, ⟨hm, inferInstance⟩, fun P ⟨hP, hPp⟩ =>
        IsLocalRing.eq_maximalIdeal (hPp.isMaximal_of_ne_bot hP)⟩
    have hdvr : IsDiscreteValuationRing B := ((IsDiscreteValuationRing.TFAE B hf).out 0 3).mpr h3
    infer_instance
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
