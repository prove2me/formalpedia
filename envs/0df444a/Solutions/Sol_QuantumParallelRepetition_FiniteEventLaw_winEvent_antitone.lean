-- Prove2me | solution 1 for QuantumParallelRepetition.FiniteEventLaw.winEvent_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:14.37599+00:00
-- url     : https://prove2.me/submissions/986989c0-3040-4d80-86ab-0bc63f28b4cc

import Mathlib
import Definitions.Def_QuantumParallelRepetition

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open QuantumParallelRepetition
noncomputable section
open scoped BigOperators
open QuantumParallelRepetition.FiniteEventLaw
variable {Ω ι : Type*} [Fintype Ω]
namespace QuantumParallelRepetition.FiniteEventLaw
theorem _root_.solution [Fintype ι]
    (wins : ι → Ω → Bool) {D E : Finset ι} (h : D ⊆ E) :
    winEvent wins E ⊆ winEvent wins D := by
  classical
  intro ω hω
  have h_all : ∀ i ∈ E, wins i ω = true := by
    simpa [winEvent] using hω
  simp only [winEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun i hi => h_all i (h hi)
end QuantumParallelRepetition.FiniteEventLaw
