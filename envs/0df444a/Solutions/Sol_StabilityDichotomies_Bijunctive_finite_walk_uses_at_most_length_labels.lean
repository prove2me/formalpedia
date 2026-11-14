-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.finite_walk_uses_at_most_length_labels
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:09:08.961726+00:00
-- url     : https://prove2.me/submissions/d2973f0f-f8c8-48df-8a00-def347703267

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem walk_arc_mono {α : Type} {arc arc' : α → α → Prop}
    (h : ∀ a b, arc a b → arc' a b) {n : ℕ} {a b : α} (hw : WalkLength arc n a b) :
    WalkLength arc' n a b := by
  induction hw with
  | zero => exact WalkLength.zero _
  | step hab hbc ih => exact WalkLength.step (h _ _ hab) ih

theorem solution {α ι : Type} (arc : ι → α → α → Prop)
    (n : ℕ) (a b : α) (hw : WalkLength (fun x y => ∃ i, arc i x y) n a b) :
    ∃ S : Finset ι, S.card ≤ n ∧
      WalkLength (fun x y => ∃ i ∈ S, arc i x y) n a b := by
  classical
  induction hw with
  | zero a => exact ⟨∅,by simp,WalkLength.zero a⟩
  | @step n a b c hab hbc ih =>
    obtain ⟨i,hi⟩ := hab
    obtain ⟨S,hcard,hw⟩ := ih
    refine ⟨insert i S, ?_, ?_⟩
    · exact (Finset.card_insert_le i S).trans (Nat.succ_le_succ hcard)
    · apply WalkLength.step (b := b)
      · exact ⟨i,Finset.mem_insert_self _ _,hi⟩
      · exact walk_arc_mono (fun x y h => by
          obtain ⟨j,hj,hxy⟩ := h
          exact ⟨j,Finset.mem_insert_of_mem hj,hxy⟩) hw
