-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stageHaltTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T04:04:42.419265+00:00
-- url     : https://prove2.me/submissions/72128f7a-cf53-47cd-a9e7-09cd98be3c35

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_joint_haltTime


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
    (i : Fin n) : Measurable (stageHaltTime p n i) := by
  let f : StageMaps p i.val × StageTables p i.val → ℕ :=
    fun w => haltTime (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2
  have hf : Measurable f := measurable_joint_haltTime (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val) ℕ
    inferInstance inferInstance inferInstance f (stagePair p n i) hf (measurable_stagePair p n i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
