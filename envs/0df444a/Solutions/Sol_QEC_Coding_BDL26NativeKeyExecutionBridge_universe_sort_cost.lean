-- Prove2me | solution 1 for QEC.Coding.BDL26NativeKeyExecutionBridge.universe_sort_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:18:39.616227+00:00
-- url     : https://prove2.me/submissions/4fa85980-d2a1-4258-bd48-11f656bcc139

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_compare_actual
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_compare_cost
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleColors_nativeKey_injective
import Theorems.Thm_QEC_Coding_BDL26NativeTriangleKeys_compare_cost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_sortQuery_cost_le


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
    (J : Vertex (Presentation S n) → Space) {r : ℝ} (hr : 0 ≤ r) :
    (universeQ S n J hr).2 ≤ (rawUniverseQ S n J hr).2 +
      ((rawUniverseQ S n J hr).1.length+1)^2*159 := by
  have h := sortQuery_cost_le (compareQ S n J r)
    (fun a b => keyPriorityLE (Presentation S n) (NC.nativeKey S n) (NC.nativeKey_injective S n)
      J r (event S n J r a) (event S n J r b))
    (compare_actual S n J r) 158 (compare_cost S n J r) (rawUniverseQ S n J hr).1
  change (rawUniverseQ S n J hr).2 + (sortQuery (compareQ S n J r) _).2 ≤ _
  exact Nat.add_le_add_left h _
end QEC.Coding.BDL26NativeKeyExecutionBridge
