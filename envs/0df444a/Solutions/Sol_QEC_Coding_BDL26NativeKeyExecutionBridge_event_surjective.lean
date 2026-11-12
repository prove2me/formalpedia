-- Prove2me | solution 1 for QEC.Coding.BDL26NativeKeyExecutionBridge.event_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:59:29.186195+00:00
-- url     : https://prove2.me/submissions/815f5195-0e2e-4a5f-9a14-ee25cc3eeddc

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeMasterCandidates
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventUniverse
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeKeyExecutionBridge
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
    (J : Vertex (Presentation S n) → Space) (r : ℝ) :
    Function.Surjective (event S n J r) := by
  intro e
  let m : MasterEvent (Presentation S n) := ⟨e.val,e.property.1⟩
  let row := (MC.masterEquiv S n).symm m
  have he : master S n row = m := (MC.masterEquiv S n).apply_symm_apply m
  refine ⟨⟨row, ?_⟩, ?_⟩
  · rw [he]
    exact e.property
  · apply Subtype.ext
    change (master S n row).val = e.val
    exact congrArg (fun m : MasterEvent (Presentation S n) => m.val) he
end QEC.Coding.BDL26NativeKeyExecutionBridge
