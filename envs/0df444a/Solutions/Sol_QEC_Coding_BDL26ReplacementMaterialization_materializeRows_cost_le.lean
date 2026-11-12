-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.materializeRows_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:22:35.904203+00:00
-- url     : https://prove2.me/submissions/9bbf81c7-b467-4e44-9576-4a204960bc32

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_PointCode_run_cost_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_successorCode_bounds
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_mapQuery_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexInputList_length


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (R : List (Vertex (StagePresentation p n) × Space)) :
    (materializeRows p n R).2 ≤
      65536*(R.length+1)*Fintype.card (Vertex (StagePresentation p (n+1))) := by
  have hquery (v : Vertex (StagePresentation p (n+1))) :
      ((successorCode p n v).run R).2+1 ≤ 65535*(R.length+1) := by
    have hb := PointCode.run_cost_le R (successorCode p n v)
    have hc := successorCode_bounds p n v
    have hm := Nat.mul_le_mul_left (2*R.length) hc.1
    nlinarith
  have h := mapQuery_cost_le
    (fun v => let q := (successorCode p n v).run R; ((v,q.1),q.2+1))
    (vertexInputList (StagePresentation p (n+1))) (65535*(R.length+1)) (fun v _ => hquery v)
  rw [vertexInputList_length] at h
  change (materializeRows p n R).2 ≤ _
  calc
    _ ≤ Fintype.card (Vertex (StagePresentation p (n+1)))*(65535*(R.length+1)+1) := h
    _ ≤ Fintype.card (Vertex (StagePresentation p (n+1)))*(65536*(R.length+1)) :=
      Nat.mul_le_mul_left _ (by omega)
    _ = _ := by ring
end QEC.Coding.BDL26ReplacementMaterialization
