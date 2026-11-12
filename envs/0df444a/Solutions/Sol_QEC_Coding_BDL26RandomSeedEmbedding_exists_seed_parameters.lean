-- Prove2me | solution 1 for QEC.Coding.BDL26RandomSeedEmbedding.exists_seed_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:58:02.975717+00:00
-- url     : https://prove2.me/submissions/bf72d69e-7955-4ee9-a1a3-09c548b20d23

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalLocality
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_RandomizedEmbeddingStep
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_parameter_localMap
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_parameter_density
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physicalGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometricParameters_nonempty


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomSeedEmbedding
open Classical BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RandomSeedEmbedding
theorem _root_.solution (densityLower : ℝ) :
    ∃ p : GeometricParameters densityLower,
      IsBoundedDensityLocalMap (state (perturbationOddScale p) 0).presentation
        (seedPoint (perturbationOddScale p)) p.t ∧
      (∀ c, ((qubitHits (state (perturbationOddScale p) 0).presentation
        (seedPoint (perturbationOddScale p)) (Metric.closedBall c 1)).card : ℝ) ≤ 2*p.t) ∧
      PhysicalGeometry (perturbationOddScale p) 0 (seedPoint (perturbationOddScale p)) p.t := by
  obtain ⟨p⟩ := geometricParameters_nonempty densityLower
  exact ⟨p, seed_parameter_localMap p, seed_parameter_density p, seed_physicalGeometry p⟩
end QEC.Coding.BDL26RandomSeedEmbedding
