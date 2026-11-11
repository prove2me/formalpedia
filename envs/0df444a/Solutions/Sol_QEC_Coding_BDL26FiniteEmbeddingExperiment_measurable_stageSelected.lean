-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stageSelected
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:57:30.577412+00:00
-- url     : https://prove2.me/submissions/60da7da8-e368-42db-9ac3-79dc20c38c17

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_joint_selected


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
    (i : Fin n) (time : ℕ) : Measurable (stageSelected p n i time) := by
  let f : StageMaps p i.val × StageTables p i.val → Option (MasterEvent (StagePresentation p i.val)) :=
    fun w => (selected (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2 time).map
          (eventToMaster (StagePresentation p i.val) w.1 (anchorRadius p.m))
  have hf : Measurable f := measurable_joint_selected (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) time
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val)
    (Option (MasterEvent (StagePresentation p i.val))) inferInstance inferInstance inferInstance
    f (stagePair p n i) hf (measurable_stagePair p n i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
