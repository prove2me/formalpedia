-- Prove2me | solution 2 for QEC.Coding.BDL26RandomSeedEmbedding.seed_parameter_density
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T00:48:30.366001+00:00
-- url     : https://prove2.me/submissions/964e72f1-759b-45c8-89b4-1b8b4d8188c1

import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_qubit_density
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_five_le_twice_parameter
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

theorem solution {L : ℝ} (p : GeometricParameters L) (c : Space) :
    ((qubitHits (state (perturbationOddScale p) 0).presentation
      (seedPoint (perturbationOddScale p)) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t := by
  exact (seed_qubit_density (perturbationOddScale p) c).trans
    (five_le_twice_parameter p)
