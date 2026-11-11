-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stageSelected_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:39:45.894004+00:00
-- url     : https://prove2.me/submissions/ddafd5e9-a79b-43dc-853f-3dd4656311a6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment

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
    stageSelected p n i time z = none ↔
      selected (eventSupport (StagePresentation p i.val) (stageInput p n i z) (anchorRadius p.m))
        (eventBad (StagePresentation p i.val) (stageInput p n i z)
          (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) (tableAt p n i z) time = none := by
  exact Option.map_eq_none_iff
end QEC.Coding.BDL26FiniteEmbeddingExperiment
