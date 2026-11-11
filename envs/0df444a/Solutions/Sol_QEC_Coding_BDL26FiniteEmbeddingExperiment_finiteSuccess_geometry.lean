-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.finiteSuccess_geometry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:21:06.202812+00:00
-- url     : https://prove2.me/submissions/c3368729-ecc4-4265-b3a3-9c5720fda1c1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26RandomPhysicalLocality_physicalGeometry_of_localMap


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    {z : Experiment p n} (hz : z ∈ finiteSuccess p n) (i : Fin (n+1)) :
    PhysicalGeometry (perturbationOddScale p) i.val (history p n z i) p.t :=
  physicalGeometry_of_localMap _ _ _ (hz.2.2 i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
