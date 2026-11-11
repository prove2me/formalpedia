-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.history_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:29:32.91105+00:00
-- url     : https://prove2.me/submissions/24dea4e1-4055-4d49-87b3-ec64e3eeccb8

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_evaluate_prefix_succ


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n)
    (z : Experiment p n) :
    history p n z ⟨i.val+1, by omega⟩ = stagePhysicalOutput p n i z :=
  evaluate_prefix_succ p i.isLt z
end QEC.Coding.BDL26FiniteEmbeddingExperiment
