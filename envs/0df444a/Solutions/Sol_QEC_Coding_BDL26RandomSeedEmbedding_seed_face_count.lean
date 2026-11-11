-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_face_count
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T00:40:48.444721+00:00
-- url     : https://prove2.me/submissions/c7dd5455-25d6-4947-9519-73c117d868bb

import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_face_hit_iff
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_face_card
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
    (familyHits (tannerFaceImage (state S 0).presentation (seedPoint S))
      (Metric.closedBall c 1)).card =
        if (0 : Space) ∈ Metric.closedBall c 1 then 4 else 0 := by
  simp only [familyHits, seed_face_hit_iff]
  by_cases h : (0 : Space) ∈ Metric.closedBall c 1
  · simp only [h, if_true, Finset.filter_true, Finset.card_univ, seed_face_card]
  · simp [h]
