-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_face_hit_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T00:33:08.79119+00:00
-- url     : https://prove2.me/submissions/85e655fb-79c7-4e3a-8487-bde7896ba47b

import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_face_image
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

theorem solution (S : OddScale) (f : (state S 0).presentation.Face)
    (ball : Set Space) :
    (tannerFaceImage (state S 0).presentation (seedPoint S) f ∩ ball).Nonempty ↔
      (0 : Space) ∈ ball := by
  rw [seed_face_image]
  simp