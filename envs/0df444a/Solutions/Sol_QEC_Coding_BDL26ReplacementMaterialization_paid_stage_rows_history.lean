-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.paid_stage_rows_history
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T01:22:27.448168+00:00
-- url     : https://prove2.me/submissions/f608cbe5-ba0b-462e-9693-f1398a119403

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_paidSuccessorQuery_rows
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_history_stage


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (N : ℕ)
    (i : Fin N) (z : Experiment p N) :
    (paidSuccessorQuery p i.val (stageInput p N i z) (tableAt p N i z)).1 =
      (vertexInputList (StagePresentation p (i.val+1))).map
        (fun v => (v,history p N z ⟨i.val+1,by omega⟩ v)) := by
  rw [paidSuccessorQuery_rows]
  have hh := history_stage p N i z
  rw [hh]
  rfl
end QEC.Coding.BDL26ReplacementMaterialization
