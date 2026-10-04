-- Prove2me | solution 1 for ResourceScheduling.Graph.ram_frames
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-02T14:04:03.252472+00:00
-- url     : https://prove2.me/submissions/13f2993b-9039-4cd4-a5c5-38f4b2881a79

import Definitions.Def_ResourceScheduling_Graph_RAM

set_option autoImplicit false
open CookPvsNP ResourceScheduling.Graph

theorem solution {V : Type} [DecidableEq V] (s : RAMState V)
    (l : RAMWire V → List Letter) (hr : RAMRep s l) :
    (∀ v w, RAMRep (s.set v w.length) (Function.update l (ramReg v) w)) ∧
    (∀ w, RAMRep { s with word := w } (Function.update l ramInput w)) ∧
    (∀ w, RAMRep { s with out := w } (Function.update l ramOutput w)) ∧
    (∀ v, ((l (ramReg v)).head?).isSome = decide (0 < s.val v)) := by
  rcases hr with ⟨hv, hi, ho, ht⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro v w
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      by_cases h : j = v
      · subst j; simp [RAMState.set]
      · simpa [RAMState.set, ramReg, Function.update, h] using hv j
    · simpa [RAMState.set, ramReg, ramInput] using hi
    · simpa [RAMState.set, ramReg, ramOutput] using ho
    · intro j; simpa [ramReg, ramTmp] using ht j
  · intro w
    refine ⟨?_, by simp, ?_, ?_⟩
    · intro j; simpa [ramReg, ramInput] using hv j
    · simpa [ramInput, ramOutput] using ho
    · intro j; simpa [ramInput, ramTmp] using ht j
  · intro w
    refine ⟨?_, ?_, by simp, ?_⟩
    · intro j; simpa [ramReg, ramOutput] using hv j
    · simpa [ramInput, ramOutput] using hi
    · intro j; simpa [ramOutput, ramTmp] using ht j
  · intro v
    rw [← hv v]
    cases l (ramReg v) <;> simp

#print axioms solution
