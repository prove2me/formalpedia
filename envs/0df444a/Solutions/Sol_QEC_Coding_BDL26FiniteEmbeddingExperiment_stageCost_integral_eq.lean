-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stageCost_integral_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:22:15.916306+00:00
-- url     : https://prove2.me/submissions/1fcd7e94-5b71-4604-98ae-01a18a065ea9

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_jointStageCost
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_law
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26QuantitativeBounds
open BDL26RandomPerturbation BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    (∫⁻ z, stageCost p n i z ∂experimentLaw p n) =
      ∫⁻ J, ∫⁻ T, jointStageCost p i.val (J,T)
        ∂physicalTableLaw p i.val ∂outputLaw p i.val := by
  calc
    _ = ∫⁻ w, jointStageCost p i.val w
        ∂(experimentLaw p n).map (stagePair p n i) :=
      (lintegral_map (measurable_jointStageCost p i.val) (measurable_stagePair p n i)).symm
    _ = _ := by
      rw [stagePair_law]
      exact lintegral_prod _ (measurable_jointStageCost p i.val).aemeasurable
end QEC.Coding.BDL26FiniteEmbeddingExperiment
