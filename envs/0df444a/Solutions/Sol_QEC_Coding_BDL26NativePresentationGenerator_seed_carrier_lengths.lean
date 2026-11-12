-- Prove2me | solution 1 for QEC.Coding.BDL26NativePresentationGenerator.seed_carrier_lengths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:58:09.594207+00:00
-- url     : https://prove2.me/submissions/9aa6f0eb-0000-423d-b7ce-cc6afce7942c

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
theorem _root_.solution :
    seedFrame.xs.length=2 ∧ seedFrame.qs.length=5 ∧ seedFrame.zs.length=2 ∧
      seedFrame.faces.length=4 := by decide
end QEC.Coding.BDL26NativePresentationGenerator
