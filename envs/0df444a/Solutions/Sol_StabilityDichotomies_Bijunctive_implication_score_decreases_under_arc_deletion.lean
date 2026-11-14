-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.implication_score_decreases_under_arc_deletion
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T09:03:44.843864+00:00
-- url     : https://prove2.me/submissions/dddf3386-d3bd-4ff9-b1c6-4be33a753c63

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem walk_mono {α : Type} {arc arc' : α → α → Prop}
    (hsub : ∀ a b, arc' a b → arc a b) {n : ℕ} {a b : α}
    (hw : WalkLength arc' n a b) : WalkLength arc n a b := by
  induction hw with
  | zero => exact WalkLength.zero _
  | step hab hw ih => exact WalkLength.step (hsub _ _ hab) ih

private theorem distance_mono {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (G G' : Instance Γ V) (hsub : ∀ a b, implicationArc rep G' a b → implicationArc rep G a b)
    (a b : Literal V) (n : ℕ) (hd : implicationDistance rep G' a b = some n) :
    ∃ m, implicationDistance rep G a b = some m ∧ m ≤ n := by
  unfold implicationDistance at hd
  split_ifs at hd with hreach
  · have hn : Nat.find hreach = n := by simpa using hd
    have hw : WalkLength (implicationArc rep G') n a b := by simpa [← hn] using Nat.find_spec hreach
    have hw' := walk_mono hsub hw
    have hreach' : ∃ m, WalkLength (implicationArc rep G) m a b := ⟨n,hw'⟩
    refine ⟨Nat.find hreach', ?_, Nat.find_min' hreach' hw'⟩
    simp [implicationDistance,hreach']

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G G' F : Instance Γ V) (δ : Literal V → ℝ)
    (hsub : ∀ a b, implicationArc rep G' a b → implicationArc rep G a b)
    (target : Literal V) : literalScore rep G' F δ target ≤ literalScore rep G F δ target := by
  unfold literalScore
  apply Finset.sup_le
  intro root hr
  by_cases hf : feasibleLiteral F root
  · cases hd : implicationDistance rep G' root target with
    | none => simp [hf,hd]
    | some n =>
      obtain ⟨m,hm,hmn⟩ := distance_mono rep G G' hsub root target n hd
      apply Finset.le_sup_of_le (Finset.mem_univ root)
      simp only [hf, ↓reduceIte, hd, hm]
      have hc : (m : ℝ) ≤ n := by exact_mod_cast hmn
      exact_mod_cast (show δ root - n ≤ δ root - m by linarith)
  · simp [hf]
