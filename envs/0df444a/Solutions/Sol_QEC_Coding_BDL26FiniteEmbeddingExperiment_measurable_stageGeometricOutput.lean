-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stageGeometricOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:57:48.667657+00:00
-- url     : https://prove2.me/submissions/78121238-efa1-4805-9da8-f0ac65cf885a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_joint_geometricOutput


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) : Measurable (stageGeometricOutput p n i) := by
  let f : StageMaps p i.val × StageTables p i.val → StageMaps p i.val :=
    fun w => geometricOutput (StagePresentation p i.val) w.1 p w.2
  have hf : Measurable f := measurable_joint_geometricOutput (StagePresentation p i.val) p
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val) (StageMaps p i.val)
    inferInstance inferInstance inferInstance f (stagePair p n i) hf (measurable_stagePair p n i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
