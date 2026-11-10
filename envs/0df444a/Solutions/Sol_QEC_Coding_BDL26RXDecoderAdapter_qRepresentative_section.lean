-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.qRepresentative_section
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:41:50.505009+00:00
-- url     : https://prove2.me/submissions/ebce85d9-7a9a-4adc-9aaa-a0030c4adbd9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Coordinates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Representative
import Theorems.Thm_QEC_Coding_BDL26RXDecoderAdapter_localCqCoordinate_mk

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open BDL26ReplacementSupport BDL26ReplacementCochainMaps BDL26RXStagedRestriction
open BDL26DecodingGraph MultiscaleDecoder
open scoped Classical BigOperators
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q)
    (h : (localCq P S q).middleCohomology) :
    (localCq P S q).middleCoboundaryInCocycles.mkQ (qRepresentative P A S q h) = h := by
  apply (localCqCohomologyEquiv P A S q).injective
  change localCqCohomologyEquiv P A S q
    (Submodule.Quotient.mk (qRepresentative P A S q h)) = localCqCohomologyEquiv P A S q h
  rw [localCqCoordinate_mk]
  rfl
end QEC.Coding.BDL26RXDecoderAdapter
