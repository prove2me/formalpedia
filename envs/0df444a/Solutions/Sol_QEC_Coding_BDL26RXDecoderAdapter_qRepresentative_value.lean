-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qRepresentative_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T02:20:08.192389+00:00
-- url     : https://prove2.me/submissions/5e6e3edf-956f-48e8-9f1e-b2356e2fb1d1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (w : Word BDL26Field P.Q)
    (p : LocalRegionIndex ((localQ P S).correctionRegion q)) :
    (qRepresentative P A S q ((qCohomologyEquiv P A S).symm w q)).1 p = w q := by
  change localCqCohomologyEquiv P A S q
    ((localCqCohomologyEquiv P A S q).symm (w q)) = w q
  exact LinearEquiv.apply_symm_apply _ _
end QEC.Coding.BDL26RXDecoderAdapter
