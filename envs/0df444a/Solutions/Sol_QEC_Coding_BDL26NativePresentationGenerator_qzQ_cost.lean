-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.qzQ_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:54:29.912386+00:00
-- url     : https://prove2.me/submissions/7d94c0e1-a8c8-42a9-92f9-99b637d6d064

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_BoundedValenceSuccessors
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_QuantitativeBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_NativePresentationGenerator
import Theorems.Thm_QEC_Coding_BDL26NativePresentationGenerator_anyQ_cost

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26NativePresentationGenerator
open BDL26FiniteTannerSquare BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RXLocalReplacement hiding Two
open BDL26QuantitativeBounds BDL26BoundedValence
open BDL26RandomPerturbation
namespace QEC.Coding.BDL26NativePresentationGenerator
theorem _root_.solution (F : Frame) (q z : ℕ) : (qzQ F q z).2 = 9*F.faces.length :=
  anyQ_cost _ _ 8 (by intro f hf; rfl)
end QEC.Coding.BDL26NativePresentationGenerator
