-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.seed_xq_literal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:00:21.380208+00:00
-- url     : https://prove2.me/submissions/b4f402c3-c69a-4b49-b34c-c06ac206d94f

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
theorem _root_.solution (x : Fin 2) (q : Fin 5) :
    (xqQ seedFrame x.val q.val).1=baseTannerSquarePresentation.xq x q :=
  refines_xq seedRefines baseTannerSquareAdmissible x q
end QEC.Coding.BDL26NativePresentationGenerator
