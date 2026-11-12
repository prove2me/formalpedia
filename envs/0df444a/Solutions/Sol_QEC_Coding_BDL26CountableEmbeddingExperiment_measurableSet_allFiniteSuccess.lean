-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.measurableSet_allFiniteSuccess
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:44:11.702195+00:00
-- url     : https://prove2.me/submissions/8bff8f26-5aa4-47a7-8cc8-1fbd94a65490

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_allFiniteSuccess_eq_iInter
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurableSet_finiteSuccess


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) :
    MeasurableSet (allFiniteSuccess p) := by
  rw [allFiniteSuccess_eq_iInter]
  exact MeasurableSet.iInter (fun n =>
    (measurableSet_finiteSuccess p n).preimage (measurable_truncate p n))
end QEC.Coding.BDL26CountableEmbeddingExperiment
