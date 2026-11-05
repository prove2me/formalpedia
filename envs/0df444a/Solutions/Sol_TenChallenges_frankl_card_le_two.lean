-- Prove2me | solution 1 for TenChallenges.frankl_card_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:20:23.136825+00:00
-- url     : https://prove2.me/submissions/4991d2b8-b878-4ee3-8cb5-8a6ea7fc0021

import Definitions.Def_TenChallenges_Challenge_09
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-- Every nondegenerate family with at most two members has a half-dense element.
Union closure is not needed for this small case. -/
theorem solution {U : Type*} [DecidableEq U] (F : Finset (Finset U))
    (hne : Nondegenerate F) (hcard : F.card ≤ 2) :
    ∃ x : U, (1 / 2 : ℚ) ≤ density F x := by
  classical
  have hex : ∃ A ∈ F, A.Nonempty := by
    by_contra h
    have hsub : F ⊆ {∅} := by
      intro A hA
      simp only [Finset.mem_singleton]
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact h ⟨A, hA, x, hx⟩
    have hnon : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne.1
    exact hne.2 (Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hnon, fun A hA => by simpa using hsub hA⟩)
  obtain ⟨A, hAF, x, hxA⟩ := hex
  refine ⟨x, ?_⟩
  have hocc : 1 ≤ occurrences F x := by
    exact Finset.card_pos.mpr ⟨A, Finset.mem_filter.mpr ⟨hAF, hxA⟩⟩
  have hcpos : 0 < F.card := Finset.card_pos.mpr ⟨A, hAF⟩
  unfold density
  rw [max_eq_right (by omega : 1 ≤ F.card)]
  apply (le_div_iff₀ (by positivity : (0 : ℚ) < F.card)).mpr
  have h1 : (1 : ℚ) ≤ occurrences F x := by exact_mod_cast hocc
  have h2 : (F.card : ℚ) ≤ 2 := by exact_mod_cast hcard
  linarith
