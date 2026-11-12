-- Prove2me | solution 1 for QEC.Coding.BDL26ReplacementMaterialization.stageMaterializationCost_le_final
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T07:37:25.675275+00:00
-- url     : https://prove2.me/submissions/2000607c-4227-48e3-843b-02d0c8cd30b5

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperimentCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperimentGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ReplacementMaterialization
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_materializationCost_le
import Theorems.Thm_QEC_Coding_BDL26ReplacementMaterialization_stageVertices_le_qubits
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_stageQubits_mono
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    stageMaterializationCost p N i z ≤ 65536*65^2*(stageQubits p N+1)^2 := by
  have hb := materializationCost_le p i.val (stagePair p N i z)
  have hv0 := stageVertices_le_qubits p i.val
  have hv1 := stageVertices_le_qubits p (i.val+1)
  have hq0 := stageQubits_mono p (Nat.le_of_lt i.isLt)
  have hq1 : stageQubits p (i.val+1) ≤ stageQubits p N :=
    stageQubits_mono p (by omega : i.val+1 ≤ N)
  have h0 : Fintype.card (Vertex (StagePresentation p i.val)) ≤ 65*stageQubits p N :=
    hv0.trans (Nat.mul_le_mul_left 65 hq0)
  have h1 : Fintype.card (Vertex (StagePresentation p (i.val+1))) ≤ 65*stageQubits p N :=
    hv1.trans (Nat.mul_le_mul_left 65 hq1)
  change materializationCost p i.val (stagePair p N i z) ≤ _
  calc
    _ ≤ 65536*(Fintype.card (Vertex (StagePresentation p i.val))+1)*
        Fintype.card (Vertex (StagePresentation p (i.val+1))) := hb
    _ ≤ 65536*(65*stageQubits p N+1)*(65*stageQubits p N) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.add_le_add_right h0 1)) h1
    _ ≤ _ := by nlinarith
end QEC.Coding.BDL26ReplacementMaterialization
