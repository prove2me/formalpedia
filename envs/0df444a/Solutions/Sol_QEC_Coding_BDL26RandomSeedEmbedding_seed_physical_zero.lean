-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_physical_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:20:45.297745+00:00
-- url     : https://prove2.me/submissions/c1031866-cfbb-440c-bed4-3ff315ea44a4

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomSeedEmbedding
theorem _root_.solution (S : OddScale) (q : Physical S 0) :
    seedPoint S (.q q) = 0 := rfl
end QEC.Coding.BDL26RandomSeedEmbedding
