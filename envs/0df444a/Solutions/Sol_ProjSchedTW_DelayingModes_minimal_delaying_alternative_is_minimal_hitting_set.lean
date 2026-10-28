-- Prove2me | solution 1 for ProjSchedTW.DelayingModes.minimal_delaying_alternative_is_minimal_hitting_set
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T20:12:12.791143+00:00
-- url     : https://prove2.me/submissions/09186177-d6ab-45fe-b2de-79f707b11a74

import Mathlib
import Definitions.Def_ProjSchedTW_DelayingModes_Project

open ProjSchedTW.DelayingModes

private lemma isForbidden_mono {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) {A B : Finset (Fin (n + 2))} (hAB : A ⊆ B) (hA : P.IsForbidden A) :
    P.IsForbidden B := by
  rcases hA with ⟨k, hk⟩
  exact ⟨k, lt_of_lt_of_le hk (Finset.sum_le_sum_of_subset hAB)⟩

private lemma exists_minimalForbidden_subset {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) {A : Finset (Fin (n + 2))} (hA : P.IsForbidden A) :
    ∃ F' ⊆ A, P.IsMinimalForbidden F' := by
  induction A using Finset.strongInduction with
  | H A ih =>
    by_cases hsub : ∃ B ⊂ A, P.IsForbidden B
    · rcases hsub with ⟨B, hBA, hB⟩
      rcases ih B hBA hB with ⟨F', hF'B, hF'min⟩
      exact ⟨F', Finset.Subset.trans hF'B hBA.subset, hF'min⟩
    · refine ⟨A, Finset.Subset.rfl, ⟨hA, fun B hB hBA => ?_⟩⟩
      by_contra hnot
      exact hsub ⟨B, lt_of_le_not_ge hBA hnot, hB⟩

theorem solution {n : ℕ} {K : Type} [Fintype K]
    (P : Project n K) (hP : P.StandingAssumptions) (F B : Finset (Fin (n + 2)))
    (hF : P.IsForbidden F) (hB : P.IsMinimalDelayingAlternative F B) :
    Minimal (fun H : Finset (Fin (n + 2)) =>
      ∀ F' ⊆ F, P.IsMinimalForbidden F' → (H ∩ F').Nonempty) B := by
  refine ⟨?_, ?_⟩
  · intro F' hF'F hF'min
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    have hsub : F' ⊆ F \ B := by
      intro x hx
      rw [Finset.mem_sdiff]
      refine ⟨hF'F hx, ?_⟩
      intro hxB
      have : x ∈ B ∩ F' := Finset.mem_inter.mpr ⟨hxB, hx⟩
      rw [hne] at this
      simp at this
    exact hB.prop.2 (isForbidden_mono P hsub hF'min.prop)
  · intro H hH hHB
    have hHF : H ⊆ F := Finset.Subset.trans hHB hB.prop.1
    have hfeas : P.IsFeasibleSet (F \ H) := by
      intro hforb
      obtain ⟨F', hF'sub, hF'min⟩ := exists_minimalForbidden_subset P hforb
      have hF'F : F' ⊆ F := Finset.Subset.trans hF'sub Finset.sdiff_subset
      obtain ⟨x, hx⟩ := hH F' hF'F hF'min
      rw [Finset.mem_inter] at hx
      have hx_sdiff : x ∈ F \ H := hF'sub hx.2
      exact (Finset.mem_sdiff.mp hx_sdiff).2 hx.1
    exact hB.le_of_le ⟨hHF, hfeas⟩ hHB
