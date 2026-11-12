-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.prefixStageCost_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:34:28.537069+00:00
-- url     : https://prove2.me/submissions/e08f94ac-3365-4033-9a37-b9ad53fadc11

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_prefixStageCost_succ

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteEmbeddingExperiment BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (omega : Omega p) :
    Monotone (fun N => prefixStageCost p N omega) := by
  apply monotone_nat_of_le_succ
  intro N
  rw [prefixStageCost_succ]
  exact le_add_right le_rfl
end QEC.Coding.BDL26CountableEmbeddingExperiment
