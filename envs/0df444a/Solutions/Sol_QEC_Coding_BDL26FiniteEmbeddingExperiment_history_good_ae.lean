-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.history_good_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:08:59.943885+00:00
-- url     : https://prove2.me/submissions/7849c64d-4182-409d-95db-5db9e0ee64e6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_good_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_prefix
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_prefix_output_law


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26CSSHamiltonian
open Semantics Semantics.Davies
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin (n+1)) :
    ∀ᵐ z ∂experimentLaw p n,
      IsBoundedDensityLocalMap (StagePresentation p i.val) (history p n z i) p.t := by
  have h := outputLaw_good_ae p i.val
  rw [← prefix_output_law p (show i.val ≤ n by omega)] at h
  exact ae_of_ae_map ((measurable_evaluate p i.val).comp
    (measurable_prefix p (show i.val ≤ n by omega))).aemeasurable h
end QEC.Coding.BDL26FiniteEmbeddingExperiment
