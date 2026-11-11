-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.seed_physicalGeometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:03:20.003376+00:00
-- url     : https://prove2.me/submissions/12a7f231-2c8e-4dce-840d-c5964e08de56

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_parameter_localMap
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_physicalGeometry_of_localMap


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomSeedEmbedding
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    PhysicalGeometry (perturbationOddScale p) 0 (seedPoint (perturbationOddScale p)) p.t :=
  physicalGeometry_of_localMap _ _ _ (seed_parameter_localMap p)
end QEC.Coding.BDL26RandomSeedEmbedding
