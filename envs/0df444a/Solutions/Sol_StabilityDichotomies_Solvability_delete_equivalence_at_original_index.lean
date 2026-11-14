-- Prove2me | solution 1 for StabilityDichotomies.Solvability.delete_equivalence_at_original_index
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:31:33.265193+00:00
-- url     : https://prove2.me/submissions/5a2a0e26-47cd-40c6-913f-e49d4b71e09f

import Theorems.Thm_StabilityDichotomies_Solvability_delete_occurrence_equivalence
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability

theorem solution {Γ : Language} {V : Type} (I : Instance Γ V)
    (j : Fin I.constraints.card) :
    ∃ e : Fin I.constraints.card ≃ Option (Fin (I.delete (occurrenceAt I j)).constraints.card),
      e j = none ∧
      ∀ k, (e k).elim (occurrenceAt I j) (occurrenceAt (I.delete (occurrenceAt I j))) = occurrenceAt I k := by
  have hc : occurrenceAt I j ∈ I.constraints := by
    unfold occurrenceAt
    exact Multiset.mem_toList.mp (List.get_mem _ _)
  obtain ⟨e,he⟩ := delete_occurrence_equivalence I (occurrenceAt I j) hc
  let i := e.symm none
  have hi : occurrenceAt I i = occurrenceAt I j := by
    have h := he i
    simpa [i] using h.symm
  have hswap (k : Fin I.constraints.card) :
      occurrenceAt I ((Equiv.swap j i) k) = occurrenceAt I k := by
    by_cases hk : k = j
    · subst k
      simpa using hi
    · by_cases hk' : k = i
      · subst k
        simpa using hi.symm
      · simp [Equiv.swap_apply_of_ne_of_ne hk hk']
  let e' := (Equiv.swap j i).trans e
  refine ⟨e', ?_, ?_⟩
  · simp [e', i]
  · intro k
    change (e ((Equiv.swap j i) k)).elim (occurrenceAt I j)
      (occurrenceAt (I.delete (occurrenceAt I j))) = occurrenceAt I k
    rw [he, hswap]
