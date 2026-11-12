-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.allFiniteSuccess_source_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:39:15.042195+00:00
-- url     : https://prove2.me/submissions/c0d5d497-8b92-433a-bb44-7d4df3ee785d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_geometry

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26ReplacementEmbedding BDL26RandomPerturbation BDL26RandomPhysicalLocality
open BDL26CSSHamiltonian Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    {omega : Omega p} (h : omega ∈ allFiniteSuccess p) (k : ℕ) :
    PhysicalGeometry (perturbationOddScale p) (2*k) (levelMap p omega (2*k)) p.t :=
  allFiniteSuccess_geometry p h (2*k)
end QEC.Coding.BDL26CountableEmbeddingExperiment
