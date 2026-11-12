-- Prove2me | solution 1 for QEC.Coding.BDL26NativeKeyExecutionBridge.anchor_actual
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:16:48.533379+00:00
-- url     : https://prove2.me/submissions/d2ae649c-5def-424a-b668-7d8a6cde1b05

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_anchorFold_mem
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_anchorFold_min
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyAnchor_unique
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeKeyExecutionBridge
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace QEC.Coding.BDL26NativeKeyExecutionBridge
theorem _root_.solution (S : OddScale) (n : ℕ)
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (row : LiveRow S n J r) :
    (anchorCodeQ row.val.val.1).1 = MD.triangleCode S n
      (keyAnchor (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
        J r (event S n J r row)) := by
  have hrep := row_rep S n row.val
  have hm : (anchorCodeQ row.val.val.1).1 ∈ MC.codeList row.val.val.1 :=
    anchorFold_mem _ _
  obtain ⟨a,ha,he⟩ := (hrep _).mp hm
  have hmin : ∀ b ∈ (event S n J r row).val, NC.nativeKey S n a ≤ NC.nativeKey S n b := by
    intro b hb
    have h := anchorFold_min row.val.val.1.first
      [row.val.val.1.second,row.val.val.1.third,row.val.val.1.fourth]
      (MD.triangleCode S n b) ((hrep _).mpr ⟨b,hb,rfl⟩)
    change 2*(anchorCodeQ row.val.val.1).1.owner+(anchorCodeQ row.val.val.1).1.copy ≤ _ at h
    rw [← he] at h
    exact h
  have hanchor := keyAnchor_unique (Presentation S n) (NC.nativeKey S n)
    (NC.nativeKey_injective S n) J r (event S n J r row) a ha hmin
  exact he.symm.trans (congrArg (MD.triangleCode S n) hanchor.symm)
end QEC.Coding.BDL26NativeKeyExecutionBridge
