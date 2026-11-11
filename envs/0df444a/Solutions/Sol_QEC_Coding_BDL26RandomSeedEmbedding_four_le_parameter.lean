-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.four_le_parameter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:31:50.349199+00:00
-- url     : https://prove2.me/submissions/adf90d14-735f-4551-9595-93509a5852b4

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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) : (4 : ℝ) ≤ p.t := by
  have h := p.triangle_density
  norm_num [triangleDensityBound] at h
  linarith
end QEC.Coding.BDL26RandomSeedEmbedding
