-- Prove2me | solution 1 for RoundRobinEq.CancelableBluff.lemma_2_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:56:55.067656+00:00
-- url     : https://prove2.me/submissions/f1584ff9-f149-4811-acbe-dd5e8a67a24a

import Mathlib
import Definitions.Def_RoundRobinEq_CancelableBluff_Setting
set_option autoImplicit false
open RoundRobinEq.CancelableBluff

theorem solution {M : Type*} [DecidableEq M] (v : Finset M → ℝ) (hv : IsCancelable v)
    (S T R : Finset M) (hR : Disjoint R (S ∪ T)) :
    (v (T ∪ R) < v (S ∪ R) → v T < v S) ∧
      (v T ≤ v S → v (T ∪ R) ≤ v (S ∪ R)) ∧
      (v S = v T → v (S ∪ R) = v (T ∪ R)) := by
  have key : ∀ (S T R : Finset M), Disjoint R (S ∪ T) → v (T ∪ R) < v (S ∪ R) → v T < v S := by
    intro S T R
    induction R using Finset.induction_on with
    | empty => intro _ h; simpa using h
    | insert g R' hg ih =>
      intro hd h
      have hdd : Disjoint R' (S ∪ T) := (Finset.disjoint_of_subset_left (Finset.subset_insert g R') hd)
      have hgST : g ∉ S ∪ T := by
        intro hmem
        exact (Finset.disjoint_left.mp hd (Finset.mem_insert_self g R')) hmem
      have hgS' : g ∉ (S ∪ R') ∪ (T ∪ R') := by
        intro hmem
        simp only [Finset.mem_union, not_or] at hgST
        simp only [Finset.mem_union] at hmem
        rcases hmem with (h1 | h1) | (h2 | h2)
        · exact hgST.1 h1
        · exact hg h1
        · exact hgST.2 h2
        · exact hg h2
      have h' : v (insert g (T ∪ R')) < v (insert g (S ∪ R')) := by
        have e1 : T ∪ insert g R' = insert g (T ∪ R') := by
          ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
        have e2 : S ∪ insert g R' = insert g (S ∪ R') := by
          ext x; simp only [Finset.mem_union, Finset.mem_insert]; tauto
        rwa [e1, e2] at h
      exact ih hdd (hv (S ∪ R') (T ∪ R') g hgS' h')
  have H1 : v (T ∪ R) < v (S ∪ R) → v T < v S := key S T R hR
  have H2 : ∀ (S T : Finset M), Disjoint R (S ∪ T) → v T ≤ v S → v (T ∪ R) ≤ v (S ∪ R) := by
    intro S T hd hle
    by_contra hcon
    push_neg at hcon
    have hd' : Disjoint R (T ∪ S) := by rwa [Finset.union_comm]
    have := key T S R hd' hcon
    linarith
  refine ⟨H1, H2 S T hR, ?_⟩
  intro heq
  have hR' : Disjoint R (T ∪ S) := by rwa [Finset.union_comm]
  exact le_antisymm (H2 T S hR' heq.le) (H2 S T hR heq.ge)
