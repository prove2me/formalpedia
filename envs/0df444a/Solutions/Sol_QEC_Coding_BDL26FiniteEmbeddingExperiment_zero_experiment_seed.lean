-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.zero_experiment_seed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:29:39.505239+00:00
-- url     : https://prove2.me/submissions/a4795911-daaf-4122-b66a-91134fe4ddfd

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_physicalGeometry


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (z : Experiment p 0) :
    evaluate p 0 z = BDL26RandomSeedEmbedding.seedPoint (perturbationOddScale p) ∧
    PhysicalGeometry (perturbationOddScale p) 0 (evaluate p 0 z) p.t :=
  ⟨rfl, BDL26RandomSeedEmbedding.seed_physicalGeometry p⟩
end QEC.Coding.BDL26FiniteEmbeddingExperiment
