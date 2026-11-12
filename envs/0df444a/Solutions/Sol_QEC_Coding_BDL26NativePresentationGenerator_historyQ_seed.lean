-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.historyQ_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:59:16.42472+00:00
-- url     : https://prove2.me/submissions/444cdfec-e04d-4d97-ba06-68c6a7ecc208

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
namespace QEC.Coding.BDL26NativePresentationGenerator
theorem _root_.solution (S : OddScale) : (historyQ S 0).1=[seedFrame] := rfl
end QEC.Coding.BDL26NativePresentationGenerator
