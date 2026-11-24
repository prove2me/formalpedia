-- Prove2me | solution 1 for QuadraticProbe717.Insertion.occupied_set_monotonicity
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-23T22:30:06.38154+00:00
-- url     : https://prove2.me/submissions/32ff9b9f-14ec-4d99-b67d-1a182f90b234

import Definitions.Def_QuadraticProbe717_Insertion_probing
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
open QuadraticProbe717.Insertion

/-- One first-empty insertion step is monotone in the occupied set. -/
private lemma insertAlong_mono {α : Type*} [DecidableEq α] {A B : Finset α} (hAB : A ⊆ B)
    (probes : List α) : insertAlong A probes ⊆ insertAlong B probes := by
  -- `insertAlong B probes` always contains `B`.
  have hBsub : B ⊆ insertAlong B probes := by
    unfold insertAlong
    split
    · exact le_rfl
    · exact Finset.subset_insert _ _
  unfold insertAlong
  rcases hA : probes.find? (fun x => decide (x ∉ A)) with _ | x
  · exact hAB.trans (by unfold insertAlong at hBsub; exact hBsub)
  · dsimp only
    have hxA : x ∉ A := by simpa using List.find?_some hA
    have hx_mem : x ∈ probes := List.mem_of_find?_eq_some hA
    by_cases hxB : x ∈ B
    · refine Finset.insert_subset ?_ (hAB.trans ?_)
      · unfold insertAlong at hBsub; exact hBsub hxB
      · unfold insertAlong at hBsub; exact hBsub
    · -- x is also the first probe outside B: everything before it lies in A ⊆ B.
      obtain ⟨_, l₁, l₂, hsplit, hpre⟩ := List.find?_eq_some_iff_append.mp hA
      have hB : probes.find? (fun x => decide (x ∉ B)) = some x := by
        rw [List.find?_eq_some_iff_append]
        refine ⟨by simpa using hxB, l₁, l₂, hsplit, ?_⟩
        intro a ha
        have h1 := hpre a ha
        have hmA : a ∈ A := by simpa using h1
        simpa using hAB hmA
      rw [hB]
      exact Finset.insert_subset_insert x hAB

theorem solution {α : Type*} [DecidableEq α]
    (A B : Finset α) (hAB : A ⊆ B) (sequences : List (List α)) (t : ℕ) :
    runFrom A sequences t ⊆ runFrom B sequences t := by
  unfold runFrom
  generalize sequences.take t = l
  induction l generalizing A B with
  | nil => exact hAB
  | cons p l ih => exact ih _ _ (insertAlong_mono hAB p)
