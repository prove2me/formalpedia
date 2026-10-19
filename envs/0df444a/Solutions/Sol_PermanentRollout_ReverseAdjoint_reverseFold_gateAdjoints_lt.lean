-- Prove2me | solution 1 for PermanentRollout.ReverseAdjoint.reverseFold_gateAdjoints_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:05.100639+00:00
-- url     : https://prove2.me/submissions/7a1dc116-986a-43bc-9b5b-deff7c073b5f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_ReverseAdjoint_step_gateAdjoints_lt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
noncomputable section
open scoped BigOperators
open PermanentRollout.ReverseAdjoint
namespace PermanentRollout.ReverseAdjoint
theorem _root_.solution {ι : Type*}
    (program : List (FreeAffineInstruction ι))
    (values : Array (MvPolynomial ι ℂ)) (start : ℕ)
    (state : ReverseAdjoint ι)
    (hvalid : ∀ instruction ∈ program.zipIdx start,
      instruction.1.referencesBounded instruction.2)
    (hstate : ∀ index, state.gateAdjoints index ≠ 0 →
      index < start + program.length) :
    ∀ index,
      (((program.zipIdx start).reverse).foldl (step values)
        state).gateAdjoints index ≠ 0 → index < start := by
  induction program generalizing start state with
  | nil =>
    simpa using hstate
  | cons instruction rest ih =>
    have hhead : instruction.referencesBounded start := by
      apply hvalid (instruction, start)
      simp
    have hrest : ∀ gate ∈ rest.zipIdx (start + 1),
        gate.1.referencesBounded gate.2 := by
      intro gate hgate
      apply hvalid gate
      simp [hgate]
    have hbound : ∀ index, state.gateAdjoints index ≠ 0 →
        index < (start + 1) + rest.length := by
      intro index hindex
      have hindex' := hstate index hindex
      simp only [List.length_cons] at hindex'
      omega
    have hmid := ih (start + 1) state hrest hbound
    simp only [List.zipIdx_cons, List.reverse_cons, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    exact step_gateAdjoints_lt values
      (((rest.zipIdx (start + 1)).reverse).foldl
        (step values) state)
      instruction start hhead hmid
end PermanentRollout.ReverseAdjoint
