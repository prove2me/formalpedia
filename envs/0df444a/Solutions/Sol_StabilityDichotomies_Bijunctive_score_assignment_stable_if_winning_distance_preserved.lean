-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.score_assignment_stable_if_winning_distance_preserved
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:06:02.812503+00:00
-- url     : https://prove2.me/submissions/d2de5a71-4849-4577-88d7-353a98fd78d7

import Theorems.Thm_StabilityDichotomies_Bijunctive_implication_score_decreases_under_arc_deletion
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G G' F : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ a b, implicationArc rep G' a b → implicationArc rep G a b)
    (v : V) (w : Bool) (root : Literal V) (n : ℕ)
    (hw : w = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)))
    (hroot : feasibleLiteral F root)
    (hmax : literalScore rep G F δ (v,w) = ((δ root - n : ℝ) : WithBot ℝ))
    (hd : implicationDistance rep G' root (v,w) = some n) :
    decide (literalScore rep G' F δ (v,false) < literalScore rep G' F δ (v,true)) = w := by
  have hlow : ((δ root - n : ℝ) : WithBot ℝ) ≤ literalScore rep G' F δ (v,w) := by
    unfold literalScore
    apply Finset.le_sup_of_le (Finset.mem_univ root)
    simp [hroot,hd]
  have hmono (b : Bool) : literalScore rep G' F δ (v,b) ≤ literalScore rep G F δ (v,b) :=
    implication_score_decreases_under_arc_deletion rep G G' F δ hsub (v,b)
  have heq : literalScore rep G' F δ (v,w) = literalScore rep G F δ (v,w) :=
    le_antisymm (hmono w) (by rw [hmax]; exact hlow)
  cases w with
  | false =>
    have hnot : ¬ literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true) := by
      simpa using hw
    have hle := le_of_not_gt hnot
    have hnot' : ¬ literalScore rep G' F δ (v,false) < literalScore rep G' F δ (v,true) := by
      have h := (hmono true).trans hle
      rw [← heq] at h
      exact not_lt_of_ge h
    simp [hnot']
  | true =>
    have hgt : literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true) := by
      simpa using hw
    have hgt' : literalScore rep G' F δ (v,false) < literalScore rep G' F δ (v,true) := by
      have h := (hmono false).trans_lt hgt
      rw [← heq] at h
      exact h
    simp [hgt']
