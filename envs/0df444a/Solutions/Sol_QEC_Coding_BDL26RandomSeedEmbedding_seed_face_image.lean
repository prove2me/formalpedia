-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_face_image
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-11T00:27:09.766481+00:00
-- url     : https://prove2.me/submissions/b9c1e2b1-a01a-4f13-b5d2-a5f55fe515d7

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

theorem solution (S : OddScale) (f : (state S 0).presentation.Face) :
    tannerFaceImage (state S 0).presentation (seedPoint S) f = {(0 : Space)} := by
  simp [tannerFaceImage, seedPoint, convexHull_singleton]