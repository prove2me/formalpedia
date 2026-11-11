-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_parameter_localMap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:57:06.545225+00:00
-- url     : https://prove2.me/submissions/ba4f6ede-be73-45b7-afae-31b6356691c8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_localMap
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_four_le_parameter
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_localMap_mono


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomSeedEmbedding
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    IsBoundedDensityLocalMap (state (perturbationOddScale p) 0).presentation
      (seedPoint (perturbationOddScale p)) p.t :=
  localMap_mono _ _ (seed_localMap (perturbationOddScale p)) (four_le_parameter p)
end QEC.Coding.BDL26RandomSeedEmbedding
