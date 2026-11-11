-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_check_center_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:33:22.044011+00:00
-- url     : https://prove2.me/submissions/6c689ada-5ffa-48f2-a296-cb850348dfa9

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
theorem _root_.solution (S : OddScale) (j : Sum (ZLabel S 0) (XLabel S 0)) :
    checkCenter S 0 (seedPoint S) j = 0 := by
  cases j <;> rfl
end QEC.Coding.BDL26RandomSeedEmbedding
