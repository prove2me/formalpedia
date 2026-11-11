-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_parameter_density
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:46:52.96153+00:00
-- url     : https://prove2.me/submissions/154e1f53-adf9-4a98-9029-48d6853784f7

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_five_le_twice_parameter
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_qubit_density
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomSeedEmbedding
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (c : Space) :
    ((qubitHits (state (perturbationOddScale p) 0).presentation
      (seedPoint (perturbationOddScale p)) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t :=
  (seed_qubit_density (perturbationOddScale p) c).trans (five_le_twice_parameter p)
end QEC.Coding.BDL26RandomSeedEmbedding
