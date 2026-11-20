-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.outputLaw_good_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:00:57.4622+00:00
-- url     : https://prove2.me/submissions/9343f6f8-2a9e-4891-a550-7e08e50b8324

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_succ
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_boundedDensityLocalMap
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_successorLaw_good_ae
import Theorems.Thm_QEC_Coding_BDL26RandomSeedEmbedding_seed_parameter_localMap


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    ∀ᵐ J ∂outputLaw p n, IsBoundedDensityLocalMap (StagePresentation p n) J p.t := by
  induction n with
  | zero =>
      apply (ae_map_iff (measurable_evaluate p 0).aemeasurable
        (measurableSet_boundedDensityLocalMap (StagePresentation p 0) p.t)).mpr
      exact Filter.Eventually.of_forall (fun _ => BDL26RandomSeedEmbedding.seed_parameter_localMap p)
  | succ n ih =>
      rw [outputLaw_succ]
      exact successorLaw_good_ae p n (outputLaw p n) ih
end QEC.Coding.BDL26FiniteEmbeddingExperiment
