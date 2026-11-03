-- Prove2me | solution 1 for QuantumMaxCutEnergy.matching_dilation_four_fifths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T01:44:27.993539+00:00
-- url     : https://prove2.me/submissions/7c09ff7a-2c6a-4650-b51d-ec0da9ddfc71

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Theorems.Thm_QuantumMaxCutEnergy_small_odd_sets
import Mathlib

set_option autoImplicit false
open scoped BigOperators

/-!
# LP24's Lemma 4: the 4/5 odd-set dilation of a fractional matching

If `x ≥ 0` on the edges of a graph has vertex load at most `1` at every vertex and satisfies the
odd-set constraint for every odd set of at most `4` vertices (i.e. for the trivial singletons and for
the triangles), then `(4/5) x` satisfies *all* the odd-set constraints, so `(4/5) x` is a point of
the fractional matching polytope of Edmonds.

This is LP24 (arXiv:2401.03616) Lemma 4, obtained here as the `q = 4` instance of the proved general
dilation `QuantumMaxCutEnergy.small_odd_sets`.
-/

open QuantumMaxCutEnergy


theorem solution {n : ℕ} (x : Edge n → ℝ) (hx : ∀ e, 0 ≤ x e)
    (hload : ∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then x e else 0) ≤ 1)
    (htri : ∀ S : Finset (Fin n), Odd S.card → S.card ≤ 4 →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)), x e) ≤
        ((S.card : ℝ) - 1) / 2) :
    (∀ e, 0 ≤ ((4 : ℝ) / 5) * x e) ∧
    (∀ v : Fin n, (∑ e, if v = e.val.1 ∨ v = e.val.2 then ((4 : ℝ) / 5) * x e else 0) ≤ 1) ∧
    (∀ S : Finset (Fin n), Odd S.card →
      (∑ e ∈ (Finset.univ.filter (fun e : Edge n => e.val.1 ∈ S ∧ e.val.2 ∈ S)),
        ((4 : ℝ) / 5) * x e) ≤ ((S.card : ℝ) - 1) / 2) := by
  have h := small_odd_sets 4 x hx hload htri
  refine ⟨?_, ?_, ?_⟩
  · intro e
    have := h.1 e
    convert this using 2
    norm_num
  · intro v
    have := h.2.1 v
    convert this using 2
    norm_num
  · intro S hS
    have := h.2.2 S hS
    convert this using 2
    norm_num


#print axioms solution
