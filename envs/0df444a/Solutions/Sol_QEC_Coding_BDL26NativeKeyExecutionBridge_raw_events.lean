-- Prove2me | solution 1 for QEC.Coding.BDL26NativeKeyExecutionBridge.raw_events
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:05:53.258802+00:00
-- url     : https://prove2.me/submissions/9e7ec560-3983-4832-9ba0-98c30191f82f

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_event_injective
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_raw_mem
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_raw_nodup
import Theorems.Thm_QEC_Coding_BDL26NativeKeyExecutionBridge_event_surjective

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
theorem _root_.solution (S : OddScale) (n : ℕ) (J : Vertex (Presentation S n) → Space)
    {r : ℝ} (hr : 0 ≤ r) :
    ((rawUniverseQ S n J hr).1.map (event S n J r)).Nodup ∧
      ((rawUniverseQ S n J hr).1.map (event S n J r)).toFinset = Finset.univ := by
  refine ⟨(raw_nodup S n J hr).map (event_injective S n J r), ?_⟩
  apply Finset.eq_univ_of_forall
  intro e
  obtain ⟨row,rfl⟩ := event_surjective S n J r e
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row,raw_mem S n J hr row,rfl⟩)
end QEC.Coding.BDL26NativeKeyExecutionBridge
