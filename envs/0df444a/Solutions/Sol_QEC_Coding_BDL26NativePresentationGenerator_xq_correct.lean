-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.xq_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:47:59.889263+00:00
-- url     : https://prove2.me/submissions/d855328f-29e6-4c24-8596-8fe1c2ee5f4f

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
theorem _root_.solution (S : OddScale) (n : ℕ) (x : (state S n).presentation.X)
    (q : (state S n).presentation.Q) :
    (xqQ (generateQ S n).1 ((generatedRefines S n).xIndex x).val
      ((generatedRefines S n).qIndex q).val).1=(state S n).presentation.xq x q :=
  refines_xq (generatedRefines S n) (state S n).admissible.toTannerSquareAdmissible x q
end QEC.Coding.BDL26NativePresentationGenerator
