-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.graph_deletion_sensitive_indices_have_short_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:09:10.266014+00:00
-- url     : https://prove2.me/submissions/02be602d-f3e8-499f-92f6-b304ba6c5c71

import Theorems.Thm_StabilityDichotomies_Bijunctive_finite_walk_uses_at_most_length_labels
import Theorems.Thm_StabilityDichotomies_Bijunctive_score_assignment_stable_if_winning_distance_preserved
import Theorems.Thm_StabilityDichotomies_Bijunctive_shortest_distance_preserved_if_path_survives
import Theorems.Thm_StabilityDichotomies_Bijunctive_positive_score_has_short_winning_path
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem walk_arc_mono {α : Type} {arc arc' : α → α → Prop}
    (h : ∀ a b, arc a b → arc' a b) {n : ℕ} {a b : α} (hw : WalkLength arc n a b) :
    WalkLength arc' n a b := by
  induction hw with
  | zero => exact WalkLength.zero _
  | step hab hbc ih => exact WalkLength.step (h _ _ hab) ih

private theorem distance_walk {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (G : Instance Γ V) (a b : Literal V) (n : ℕ)
    (hd : implicationDistance rep G a b = some n) : WalkLength (implicationArc rep G) n a b := by
  unfold implicationDistance at hd
  split at hd
  next h =>
    have hn : Nat.find h = n := Option.some.inj hd
    simpa [← hn] using Nat.find_spec h
  next h => simp at hd

theorem solution
    {Γ : Language} {V ι : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (Gdel : ι → Instance Γ V)
    (δ : Literal V → ℝ) (label : ι → Literal V → Literal V → Prop)
    (hsub : ∀ j a b, implicationArc rep (Gdel j) a b → implicationArc rep G a b)
    (hlabel : ∀ a b, implicationArc rep G a b → ∃ j, label j a b)
    (hretain : ∀ i j a b, i ≠ j → label i a b → implicationArc rep (Gdel j) a b)
    (v : V) (w : Bool)
    (hw : w = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)))
    (hpos : (0 : WithBot ℝ) < literalScore rep G F δ (v,w)) :
    ∃ root : Literal V, ∃ n : ℕ, ∃ S : Finset ι,
      S.card ≤ n ∧ (n : ℝ) < δ root ∧
      ∀ j ∉ S, decide (literalScore rep (Gdel j) F δ (v,false) <
        literalScore rep (Gdel j) F δ (v,true)) = w := by
  classical
  obtain ⟨root,n,hf,hd,hmax,hshort⟩ := positive_score_has_short_winning_path rep G F δ (v,w) hpos
  have hwalk := distance_walk rep G root (v,w) n hd
  have hlabelwalk := walk_arc_mono hlabel hwalk
  obtain ⟨S,hcard,hpath⟩ := finite_walk_uses_at_most_length_labels label n root (v,w) hlabelwalk
  refine ⟨root,n,S,hcard,hshort,?_⟩
  intro j hj
  have hsurvive : WalkLength (implicationArc rep (Gdel j)) n root (v,w) := by
    apply walk_arc_mono ?_ hpath
    intro a b hab
    obtain ⟨i,hi,hij⟩ := hab
    have hne : i ≠ j := by intro h; subst i; exact hj hi
    exact hretain i j a b hne hij
  have hnew := shortest_distance_preserved_if_path_survives rep G (Gdel j) (hsub j) root (v,w) n hd hsurvive
  exact score_assignment_stable_if_winning_distance_preserved rep G (Gdel j) F δ (hsub j)
    v w root n hw hf hmax hnew
