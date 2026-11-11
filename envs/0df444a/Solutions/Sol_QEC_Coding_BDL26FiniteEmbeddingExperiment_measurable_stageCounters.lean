-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stageCounters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:53:48.943092+00:00
-- url     : https://prove2.me/submissions/152923f4-cfbf-401e-89be-07bb87bf886f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_joint_counters


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
    (i : Fin n) (time : ℕ) : Measurable (stageCounters p n i time) := by
  let f : StageMaps p i.val × StageTables p i.val → Counters (Vertex (StagePresentation p i.val)) :=
    fun w => counters (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2 time
  have hf : Measurable f := measurable_joint_counters (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) time
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val)
    (Counters (Vertex (StagePresentation p i.val))) inferInstance inferInstance inferInstance
    f (stagePair p n i) hf (measurable_stagePair p n i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
