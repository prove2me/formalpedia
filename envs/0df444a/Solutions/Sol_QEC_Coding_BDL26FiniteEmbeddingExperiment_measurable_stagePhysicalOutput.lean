-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_stagePhysicalOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T03:58:23.139355+00:00
-- url     : https://prove2.me/submissions/c32f3569-3cfe-48f9-9ffc-089d429cc728

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair


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
    (i : Fin n) : Measurable (stagePhysicalOutput p n i) := by
  let f : StageMaps p i.val × StageTables p i.val → StageMaps p (i.val+1) :=
    fun w => physicalSuccessorOutput p i.val w.1 w.2
  have hf : Measurable f := measurable_joint_physicalSuccessorOutput p i.val
  change Measurable (f ∘ stagePair p n i)
  exact @Measurable.comp (Experiment p n) (StageMaps p i.val × StageTables p i.val) (StageMaps p (i.val+1))
    inferInstance inferInstance inferInstance f (stagePair p n i) hf (measurable_stagePair p n i)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
