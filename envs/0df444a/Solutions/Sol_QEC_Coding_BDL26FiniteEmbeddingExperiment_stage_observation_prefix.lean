-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.stage_observation_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:48:38.90108+00:00
-- url     : https://prove2.me/submissions/9a5e6e0e-d0fd-415e-b157-0c58ac7deb9d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stagePair_prefix


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) {m n : ℕ}
    (h : m ≤ n) (i : Fin m) {Y : Type*}
    (F : StageMaps p i.val × StageTables p i.val → Y) (z : Experiment p n) :
    F (stagePair p m i (experimentPrefix p m n h z)) = F (stagePair p n (i.castLE h) z) :=
  congrArg F (stagePair_prefix p h i z)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
