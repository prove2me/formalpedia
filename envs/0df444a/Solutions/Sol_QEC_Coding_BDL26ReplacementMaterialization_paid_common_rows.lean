-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.paid_common_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:24:49.611457+00:00
-- url     : https://prove2.me/submissions/9f94d5d4-4dad-464e-9987-651dc10eb4d5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_paidSuccessorQuery_rows
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_levelMap_succ


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26ReplacementMaterialization
open Classical MeasureTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RXLocalReplacement BDL26RandomPerturbation BDL26FiniteEmbeddingExperiment
open BDL26RandomPhysicalLocality BDL26BoundedValence BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26ReplacementMaterialization
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (omega : BDL26CountableEmbeddingExperiment.Omega p) (n : ℕ) :
    (paidSuccessorQuery p n (BDL26CountableEmbeddingExperiment.levelMap p omega n) (omega n)).1 =
      (vertexInputList (StagePresentation p (n+1))).map
        (fun v => (v,BDL26CountableEmbeddingExperiment.levelMap p omega (n+1) v)) := by
  rw [paidSuccessorQuery_rows,BDL26CountableEmbeddingExperiment.levelMap_succ]
end QEC.Coding.BDL26ReplacementMaterialization
