-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_DegLTOfUnitSteps_degLT_diffStep_f67a5cef2aae
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:56:23.331801+00:00
-- url     : https://prove2.me/submissions/ca37eb59-85ff-4088-b640-08a549a2e338

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDegLTOfUnitSteps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace DegLTOfUnitSteps
theorem _root_.solution (h1 : DiffStepExpansion.Statement)
    (h2 : MixedDiffLinear.Statement) (h3 : DegLTClosure.Statement)
    (K : Type) [Fintype K] [DecidableEq K] (n : ℕ) (f : (K → ℤ) → ℤ)
    (hf : ∀ k, DegLT (diffStep (Pi.single k 1) f) n) (b : K → ℤ) :
    DegLT (diffStep b f) n := by
  obtain ⟨l, hl⟩ := h1 K b
  rw [hl f]
  clear hl
  induction l with
  | nil =>
    intro cs
    refine Filter.Eventually.of_forall fun m => ?_
    have h0 := (h2 K n cs f f 0 0 0).2.1
    rw [zero_smul, zero_smul] at h0
    simp only [List.map_nil, List.sum_nil]
    rw [h0]
    rfl
  | cons t l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hs : DegLT (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (diffStep (Pi.single t.1.1 1) f) f 0 t.1.2).2.2.1 (hf t.1.1)
    have hc : DegLT (t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) n :=
      (h3 K n (shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) f t.2 0).2.1 hs
    exact (h3 K n _ (List.map (fun t => t.2 • shiftFn t.1.2 (diffStep (Pi.single t.1.1 1) f)) l).sum
      0 0).1 hc ih
end DegLTOfUnitSteps
end GroundTheory.Heights₂.Heights.NumbersDVR
