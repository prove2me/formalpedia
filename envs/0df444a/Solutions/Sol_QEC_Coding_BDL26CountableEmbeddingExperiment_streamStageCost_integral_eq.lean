-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.streamStageCost_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:25:41.060058+00:00
-- url     : https://prove2.me/submissions/ff7ee224-6da7-4527-9e84-f45ae3b9e551

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentCost
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_levelMap
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_stream_freshPair_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_jointStageCost
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (i : ℕ) :
    (∫⁻ omega, streamStageCost p i omega ∂streamLaw p) =
      ∫⁻ J, ∫⁻ T, jointStageCost p i (J,T) ∂physicalTableLaw p i ∂outputLaw p i := by
  calc
    _ = ∫⁻ w, jointStageCost p i w
        ∂(streamLaw p).map (fun omega => (levelMap p omega i, omega i)) :=
      (lintegral_map (measurable_jointStageCost p i)
        ((measurable_levelMap p i).prodMk (measurable_pi_apply i))).symm
    _ = _ := by
      rw [stream_freshPair_law]
      exact lintegral_prod _ (measurable_jointStageCost p i).aemeasurable
end QEC.Coding.BDL26CountableEmbeddingExperiment
