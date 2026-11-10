-- Prove2me | solution 1 for QEC.Coding.BDL26RXDecoderAdapter.localCq_finrank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T04:30:58.435459+00:00
-- url     : https://prove2.me/submissions/9a1696e9-20ed-401c-b70d-15235567c2f2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_Reindex
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RXDecoderAdapter_LocalComplexes

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RXDecoderAdapter
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26RXLocalReplacement
open MultiscaleDecoder
open scoped Classical
namespace QEC.Coding.BDL26RXDecoderAdapter
theorem _root_.solution (P : TannerSquarePresentation)
    (A : TannerSquareAdmissible P) (S : OddScale) (q : P.Q) :
    Module.finrank BDL26Field (localCq P S q).middleCohomology = 1 := by
  rw [(localCqCohomologyEquiv P A S q).finrank_eq]
  exact Module.finrank_self BDL26Field
end QEC.Coding.BDL26RXDecoderAdapter
