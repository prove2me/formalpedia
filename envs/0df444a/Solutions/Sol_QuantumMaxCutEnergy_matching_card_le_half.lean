-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_card_le_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:08:15.702868+00:00
-- url     : https://prove2.me/submissions/66902422-f682-4a16-9fdf-e0d131b9f53d

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- A matching has at most half as many edges as there are vertices. -/
theorem solution {n : ℕ} (M : Finset (Edge n))
    (hM : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) :
    2 * M.card ≤ n := by
  classical
  set S : Finset (Fin n) := M.biUnion (fun e : Edge n => ({e.val.1, e.val.2} : Finset (Fin n)))
    with hS
  have hdisj : ∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
      Disjoint ({e.val.1, e.val.2} : Finset (Fin n)) ({e'.val.1, e'.val.2} : Finset (Fin n)) := by
    intro e he e' he' hne
    obtain ⟨h1, h2, h3, h4⟩ := hM e he e' he' hne
    rw [Finset.disjoint_left]
    intro v hv hv'
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
    rcases hv with hv | hv <;> rcases hv' with hv' | hv'
    · exact h1 (hv.symm.trans hv')
    · exact h2 (hv.symm.trans hv')
    · exact h3 (hv.symm.trans hv')
    · exact h4 (hv.symm.trans hv')
  have hcard : S.card = 2 * M.card := by
    rw [hS, Finset.card_biUnion hdisj]
    have h2 : ∀ e ∈ M, ({e.val.1, e.val.2} : Finset (Fin n)).card = 2 := fun e _ =>
      Finset.card_pair (ne_of_lt e.property)
    rw [Finset.sum_congr rfl h2, Finset.sum_const, smul_eq_mul, mul_comm]
  have hle : S.card ≤ Fintype.card (Fin n) := by
    rw [← Finset.card_univ]
    exact Finset.card_le_card (Finset.subset_univ S)
  rw [← hcard]
  simpa using hle

#print axioms solution
