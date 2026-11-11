-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stageSelected_original
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:37:57.084621+00:00
-- url     : https://prove2.me/submissions/287073c0-512b-4b84-809a-2debc0000cef

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_selected_original


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
    (i : Fin n) (time : ℕ) (z : Experiment p n) :
    stageSelected p n i time z =
      selected (masterSupport (StagePresentation p i.val))
        (masterBad (StagePresentation p i.val) (anchorRadius p.m) p.lambda
          ((6*p.m+2)*p.lambda) (stageInput p n i z)) (tableAt p n i z) time :=
  master_selected_original _ _ _ _ _ _ _
end QEC.Coding.BDL26FiniteEmbeddingExperiment
