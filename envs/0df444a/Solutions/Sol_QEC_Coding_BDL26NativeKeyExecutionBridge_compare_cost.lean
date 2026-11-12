-- Prove2me | solution 1 for QEC.Coding.BDL26NativeKeyExecutionBridge.compare_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:11:27.489207+00:00
-- url     : https://prove2.me/submissions/16f33475-397d-4b73-b006-2bd13e450bc1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_fourKey_length
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_fourKey_cost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lexLEQuery_cost_le


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
    (J : Vertex (Presentation S n) → Space) (r : ℝ) (a b : LiveRow S n J r) :
    (compareQ S n J r a b).2 ≤ 158 := by
  have ha := fourKey_cost a.val.val.1
  have hb := fourKey_cost b.val.val.1
  have hc := lexLEQuery_cost_le (fourKeyQ a.val.val.1).1 (fourKeyQ b.val.val.1).1
  rw [fourKey_length] at hc
  change (fourKeyQ a.val.val.1).2 + (fourKeyQ b.val.val.1).2 +
    (lexLEQuery (fourKeyQ a.val.val.1).1 (fourKeyQ b.val.val.1).1).2 + 1 ≤ 158
  omega
end QEC.Coding.BDL26NativeKeyExecutionBridge
