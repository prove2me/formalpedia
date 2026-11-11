-- Prove2me | solution 2 for QEC.Coding.BDL26RandomSeedEmbedding.seed_qubit_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:39:13.806235+00:00
-- url     : https://prove2.me/submissions/18f2d4c3-2190-4e6f-bc17-0c887f11b0b6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_qubit_count

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomSeedEmbedding
theorem _root_.solution (S : OddScale) (c : Space) :
    ((qubitHits (state S 0).presentation (seedPoint S) (Metric.closedBall c 1)).card : ℝ) ≤ 5 := by
  rw [seed_qubit_count]
  split_ifs <;> norm_num
end QEC.Coding.BDL26RandomSeedEmbedding
