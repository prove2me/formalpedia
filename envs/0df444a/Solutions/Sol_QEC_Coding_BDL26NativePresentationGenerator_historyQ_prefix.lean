-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.historyQ_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:58:49.27503+00:00
-- url     : https://prove2.me/submissions/7011d171-9a0d-430d-9141-d105de549329

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_historyQ_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
namespace QEC.Coding.BDL26NativePresentationGenerator
theorem _root_.solution (S : OddScale) (n : ℕ) :
    ((historyQ S (n+1)).1).take (n+1)=(historyQ S n).1 := by
  change ((historyQ S n).1 ++ [(nextFrameQ S n (lastFrameQ (historyQ S n).1).1).1]).take (n+1) = _
  exact List.take_left' (historyQ_length S n)
end QEC.Coding.BDL26NativePresentationGenerator
