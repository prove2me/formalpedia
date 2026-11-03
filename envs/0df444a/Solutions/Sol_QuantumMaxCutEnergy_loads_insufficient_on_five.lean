-- Prove2me | solution 1 for QuantumMaxCutEnergy.loads_insufficient_on_five
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T05:08:17.663024+00:00
-- url     : https://prove2.me/submissions/ab75d32c-84ea-4832-bd20-b88ad73486fe

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Theorems.Thm_QuantumMaxCutEnergy_matching_card_le_half
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- The load of a *constant* edge weight is the number of incident edges times the constant. -/
theorem loadAt_const {n : ℕ} (c : ℝ) (v : Fin n) :
    loadAt (fun _ : Edge n => c) v
      = ((Finset.univ.filter (fun e : Edge n => v = e.val.1 ∨ v = e.val.2)).card : ℝ) * c := by
  classical
  rw [loadAt, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

/-- **Loads alone do not suffice, and the odd-cycle obstruction is real.**

On the complete graph on five vertices the constant edge weight `x = 1/4` has *every vertex load equal to
`1`* — so it is a legitimate point of the fractional (star) matching polytope — and yet no integral matching
carries its total weight `∑_e w_e x_e = 10/4`: every matching has at most two edges.

This is the obstruction that the odd-set constraints remove. On a bipartite support the star constraints
already force domination (`QuantumMaxCutEnergy.matching_dominated_of_bipartite`); on `K₅` the further odd-set
constraint `∑_{e ⊆ S} x_e ≤ (|S|-1)/2` for `S` of size five is exactly what `x = 1/4` violates
(`10/4 > 2`), and it is the only such constraint available.
-/
theorem solution :
    (∀ v : Fin 5, loadAt (fun _ : Edge 5 => (1 / 4 : ℝ)) v ≤ 1) ∧
    (∀ M : Finset (Edge 5),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) →
      (∑ e ∈ M, (1 : ℝ)) < ∑ e : Edge 5, (1 : ℝ) * (1 / 4)) := by
  constructor
  · intro v
    rw [loadAt_const]
    have h : (Finset.univ.filter (fun e : Edge 5 => v = e.val.1 ∨ v = e.val.2)).card = 4 := by
      fin_cases v <;> decide
    rw [h]
    norm_num
  · intro M hM
    have hcard : 2 * M.card ≤ 5 := matching_card_le_half M hM
    have h2 : M.card ≤ 2 := by omega
    have hsum : ∑ e : Edge 5, (1 : ℝ) * (1 / 4) = 5 / 2 := by
      rw [Finset.sum_congr rfl (fun e (_ : e ∈ Finset.univ) => by norm_num : ∀ e ∈ (Finset.univ : Finset (Edge 5)), (1:ℝ) * (1/4) = 1/4)]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      have : Fintype.card (Edge 5) = 10 := by decide
      rw [this]
      norm_num
    rw [hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
    have : (M.card : ℝ) ≤ 2 := by exact_mod_cast h2
    linarith

#print axioms solution
