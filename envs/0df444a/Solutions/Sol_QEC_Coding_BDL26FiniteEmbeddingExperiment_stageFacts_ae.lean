-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stageFacts_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:09:27.802544+00:00
-- url     : https://prove2.me/submissions/fdfe6ade-4d61-4aed-9db4-f461ed3a3587

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentGeometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_outputLaw_good_ae
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_stagePair
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_law
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physical_successor_random_input_ae


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) (i : Fin n) :
    ∀ᵐ z ∂experimentLaw p n,
      PhysicalSuccessorFacts p i.val (stageInput p n i z) (tableAt p n i z) := by
  have h := physical_successor_random_input_ae p i.val (outputLaw p i.val)
    (outputLaw_good_ae p i.val)
  rw [← stagePair_law p n i] at h
  exact ae_of_ae_map (measurable_stagePair p n i).aemeasurable h
end QEC.Coding.BDL26FiniteEmbeddingExperiment
