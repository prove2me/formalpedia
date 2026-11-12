-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.seed_qz_literal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:00:24.822686+00:00
-- url     : https://prove2.me/submissions/c48a68e0-edb6-405e-b4fc-4e412f63c41f

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
theorem _root_.solution (q : Fin 5) (z : Fin 2) :
    (qzQ seedFrame q.val z.val).1=baseTannerSquarePresentation.qz q z :=
  refines_qz seedRefines baseTannerSquareAdmissible q z
end QEC.Coding.BDL26NativePresentationGenerator
