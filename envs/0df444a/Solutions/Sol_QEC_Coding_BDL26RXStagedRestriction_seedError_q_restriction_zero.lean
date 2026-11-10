-- Prove2me | solution 1 for QEC.Coding.BDL26RXStagedRestriction.seedError_q_restriction_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T01:17:44.52943+00:00
-- url     : https://prove2.me/submissions/8a6ab16b-7054-4227-bdd6-37389dc25a44

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementSupport
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_ReplacementCochainMaps
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXStagedRestriction
import Theorems.Thm_QEC_Coding_BDL26RXStagedRestriction_xBasis_q_restriction_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXStagedRestriction
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26TannerLocalRegularity
open BDL26RXLocalReplacement BDL26ReplacementSupport BDL26ReplacementCochainMaps
open MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXStagedRestriction
theorem _root_.solution (q : BaseQubit) :
    (fun vertex : QDoubleCylinderVertex baseTannerSquarePresentation q scaleFive =>
      seedError (Sum.inr ⟨q,vertex⟩)) = 0 :=
  xBasis_q_restriction_zero baseTannerSquarePresentation scaleFive (0 : BaseX) seedXEdge q
end QEC.Coding.BDL26RXStagedRestriction
