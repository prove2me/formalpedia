-- Prove2me | solution 1 for QEC.Coding.BDL26RXStagedRestriction.seedError_q_syndrome_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:14:51.643387+00:00
-- url     : https://prove2.me/submissions/ce0510bc-6d4d-49e1-bda9-90bcb3431325

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_xBasis_q_syndrome_one

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXStagedRestriction
theorem _root_.solution :
    rxCoboundary1 baseTannerSquarePresentation scaleFive seedError
      (Sum.inl (Sum.inr ⟨(0 : BaseQubit),seedQEdge⟩)) = 1 :=
  xBasis_q_syndrome_one _ _ _ _ (by decide) _
end QEC.Coding.BDL26RXStagedRestriction
