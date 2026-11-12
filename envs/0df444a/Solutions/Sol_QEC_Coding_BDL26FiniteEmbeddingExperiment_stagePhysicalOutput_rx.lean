-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stagePhysicalOutput_rx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:09:21.833743+00:00
-- url     : https://prove2.me/submissions/9a83df54-d523-430a-b963-cdcd0105955e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_physicalSuccessorOutput_rx


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
    (i : Fin n) (h : i.val % 2 = 0) (z : Experiment p n) :
    stagePhysicalOutput p n i z = fun v =>
      rxVertexPoint _ (perturbationOddScale p) (stagePerturbedOutput p n i z)
        (nextRXVertex _ i.val (state (perturbationOddScale p) i.val) h v) :=
  physicalSuccessorOutput_rx p i.val _ _ h
end QEC.Coding.BDL26FiniteEmbeddingExperiment
