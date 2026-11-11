-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.qz_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:48:10.103192+00:00
-- url     : https://prove2.me/submissions/47720710-d06c-410b-924a-81b6a8f355c9

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
theorem _root_.solution (S : OddScale) (n : ℕ) (q : (state S n).presentation.Q)
    (z : (state S n).presentation.Z) :
    (qzQ (generateQ S n).1 ((generatedRefines S n).qIndex q).val
      ((generatedRefines S n).zIndex z).val).1=(state S n).presentation.qz q z :=
  refines_qz (generatedRefines S n) (state S n).admissible.toTannerSquareAdmissible q z
end QEC.Coding.BDL26NativePresentationGenerator
