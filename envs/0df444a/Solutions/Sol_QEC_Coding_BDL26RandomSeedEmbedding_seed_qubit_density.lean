-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_qubit_density
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-10T23:35:44.331784+00:00
-- url     : https://prove2.me/submissions/85e288d1-ddee-49f4-911d-590710825ed6

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
theorem solution (S : OddScale) (c : Space) :
    ((qubitHits (state S 0).presentation (seedPoint S) (Metric.closedBall c 1)).card : ℝ) ≤ 5 := by
  have h := Finset.card_le_univ (qubitHits (state S 0).presentation (seedPoint S) (Metric.closedBall c 1))
  change (qubitHits (state S 0).presentation (seedPoint S) (Metric.closedBall c 1)).card ≤ Fintype.card (Fin 5) at h
  simp only [Fintype.card_fin] at h
  exact_mod_cast h
