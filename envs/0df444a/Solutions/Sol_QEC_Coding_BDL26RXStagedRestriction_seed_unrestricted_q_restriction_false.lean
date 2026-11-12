-- Prove2me | solution 1 for QEC.Coding.BDL26RXStagedRestriction.seed_unrestricted_q_restriction_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T22:05:47.148201+00:00
-- url     : https://prove2.me/submissions/984b6359-bbc9-44dc-84fb-fcdcf9ce1e7c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_seedError_q_restriction_zero
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_seedError_q_syndrome_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXStagedRestriction
theorem _root_.solution :
    ¬ (∀ e : Word BDL26Field (RX1 baseTannerSquarePresentation scaleFive),
      rxCoboundary1 baseTannerSquarePresentation scaleFive e
        (Sum.inl (Sum.inr ⟨(0 : BaseQubit),seedQEdge⟩)) =
      wordLinearMapTranspose (qDoubleCylinderBoundary1 baseTannerSquarePresentation
        (0 : BaseQubit) scaleFive)
        (fun vertex => e (Sum.inr ⟨(0 : BaseQubit),vertex⟩)) seedQEdge) := by
  intro h
  have he := h seedError
  rw [seedError_q_syndrome_one, seedError_q_restriction_zero, map_zero] at he
  exact one_ne_zero he
end QEC.Coding.BDL26RXStagedRestriction
