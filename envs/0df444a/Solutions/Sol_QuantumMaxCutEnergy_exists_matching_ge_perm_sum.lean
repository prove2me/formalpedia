-- Prove2me | solution 1 for QuantumMaxCutEnergy.exists_matching_ge_perm_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T03:26:59.312207+00:00
-- url     : https://prove2.me/submissions/9603cf9a-13e2-4a9a-9d58-b7320a55aa9a

import Definitions.Def_QuantumMaxCutEnergyEstimationModel
import Definitions.Def_QuantumMaxCutEdgeLoads
import Definitions.Def_QuantumMaxCutMatchingPadding
import Theorems.Thm_QuantumMaxCutEnergy_exists_matching_ge_color_sum
import Mathlib

set_option autoImplicit false
open scoped BigOperators

open QuantumMaxCutEnergy

/-- **Per-permutation matching bound.** The steps of a permutation whose endpoints have different colours
carry at most twice the weight of a single integral matching. -/
theorem solution {n : ℕ} (w x : Edge n → ℝ)
    (c : Fin n → Bool) (hc : ∀ e : Edge n, c e.val.1 ≠ c e.val.2)
    (σ : Equiv.Perm (Fin n)) (hne : ∀ a, σ a ≠ a → pairWeight x a (σ a) ≠ 0) :
    ∃ M : Finset (Edge n),
      (∀ e ∈ M, ∀ e' ∈ M, e ≠ e' →
        e.val.1 ≠ e'.val.1 ∧ e.val.1 ≠ e'.val.2 ∧ e.val.2 ≠ e'.val.1 ∧ e.val.2 ≠ e'.val.2) ∧
      ∑ a, pairWeight w a (σ a) ≤ 2 * ∑ e ∈ M, w e := by
  classical
  obtain ⟨Mf, hmatchf, hlef⟩ := exists_matching_ge_color_sum w x c hc σ false hne
  obtain ⟨Mt, hmatcht, hlet⟩ := exists_matching_ge_color_sum w x c hc σ true hne
  -- the two colour classes cover the non-fixed vertices and are disjoint
  have hdisj : Disjoint (Finset.univ.filter (fun a : Fin n => c a = false ∧ σ a ≠ a))
      (Finset.univ.filter (fun a : Fin n => c a = true ∧ σ a ≠ a)) := by
    rw [Finset.disjoint_filter]
    intro a _ h1 h2
    rw [h1.1] at h2
    exact Bool.false_ne_true h2.1
  have hunion : (Finset.univ.filter (fun a : Fin n => c a = false ∧ σ a ≠ a))
      ∪ (Finset.univ.filter (fun a : Fin n => c a = true ∧ σ a ≠ a))
      = Finset.univ.filter (fun a : Fin n => σ a ≠ a) := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨-, h⟩ | ⟨-, h⟩) <;> exact h
    · intro h
      cases hc' : c a
      · exact Or.inl ⟨rfl, h⟩
      · exact Or.inr ⟨rfl, h⟩
  have hcover : (∑ a, pairWeight w a (σ a))
      = (∑ a ∈ Finset.univ.filter (fun a : Fin n => c a = false ∧ σ a ≠ a), pairWeight w a (σ a))
        + (∑ a ∈ Finset.univ.filter (fun a : Fin n => c a = true ∧ σ a ≠ a), pairWeight w a (σ a)) := by
    rw [← Finset.sum_union hdisj, hunion]
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro a _ ha
    have hfix : σ a = a := by
      by_contra h
      exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    rw [hfix, pairWeight_self]
  rw [hcover]
  rcases le_total (∑ e ∈ Mf, w e) (∑ e ∈ Mt, w e) with hle | hle
  · refine ⟨Mt, hmatcht, ?_⟩
    nlinarith [hlef, hlet]
  · refine ⟨Mf, hmatchf, ?_⟩
    nlinarith [hlef, hlet]


#print axioms solution
