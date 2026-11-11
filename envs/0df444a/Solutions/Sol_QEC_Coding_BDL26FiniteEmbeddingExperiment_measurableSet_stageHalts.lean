-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurableSet_stageHalts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:53:20.859091+00:00
-- url     : https://prove2.me/submissions/fcf1f761-55a6-47c4-afa6-0838eec7f969

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_joint_halts


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
    (i : Fin n) : MeasurableSet {z | stageHalts p n i z} := by
  let B : Set (StageMaps p i.val × StageTables p i.val) :=
    {w | Halts (eventSupport (StagePresentation p i.val) w.1 (anchorRadius p.m))
      (eventBad (StagePresentation p i.val) w.1 (anchorRadius p.m) p.lambda
        ((6*p.m+2)*p.lambda)) w.2}
  have hB : MeasurableSet B := measurableSet_joint_halts (StagePresentation p i.val)
    (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)
  change MeasurableSet (stagePair p n i ⁻¹' B)
  exact (measurable_stagePair p n i) hB
end QEC.Coding.BDL26FiniteEmbeddingExperiment
