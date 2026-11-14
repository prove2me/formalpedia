-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.implication_score_arc_bound
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T08:06:24.695145+00:00
-- url     : https://prove2.me/submissions/05853e7f-0579-4cb5-88c7-a5cdaefbaaf8

import Definitions.Def_StabilityDichotomies_Approximability_Bijunctive
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem walk_append_arc {α : Type} {arc : α → α → Prop}
    {n : ℕ} {a b c : α} (hab : WalkLength arc n a b) (hbc : arc b c) :
    WalkLength arc (n+1) a c := by
  induction hab with
  | zero => exact WalkLength.step hbc (WalkLength.zero _)
  | @step n a b c hab hbc ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using WalkLength.step hab (ih hbc)

private theorem implication_distance_after_arc {Γ : Language} {V : Type}
    (rep : TwoCNFRepresentation Γ) (I : Instance Γ V)
    (root a b : Literal V) (n : ℕ)
    (ha : implicationDistance rep I root a = some n) (hab : implicationArc rep I a b) :
    ∃ m : ℕ, implicationDistance rep I root b = some m ∧ m ≤ n + 1 := by
  unfold implicationDistance at ha
  split_ifs at ha with hreach
  · have hn : Nat.find hreach = n := by simpa using ha
    have hw : WalkLength (implicationArc rep I) n root a := by simpa [← hn] using Nat.find_spec hreach
    have hw' := walk_append_arc hw hab
    have hreach' : ∃ m, WalkLength (implicationArc rep I) m root b := ⟨n+1,hw'⟩
    refine ⟨Nat.find hreach', ?_, Nat.find_min' hreach' hw'⟩
    simp [implicationDistance, hreach']

private theorem literal_score_candidate_lower {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (root target : Literal V) (n : ℕ) (hr : feasibleLiteral F root)
    (hd : implicationDistance rep G root target = some n) :
    ((δ root - n : ℝ) : WithBot ℝ) ≤ literalScore rep G F δ target := by
  unfold literalScore
  apply Finset.le_sup_of_le (Finset.mem_univ root)
  simp [hr,hd]

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (a b : Literal V) (hab : implicationArc rep G a b) :
    literalScore rep G F δ a ≤ literalScore rep G F δ b + ((1 : ℝ) : WithBot ℝ) := by
  unfold literalScore at *
  apply Finset.sup_le
  intro root hr
  by_cases hf : feasibleLiteral F root
  · cases hd : implicationDistance rep G root a with
    | none => simp [hf,hd]
    | some n =>
      obtain ⟨m,hm,hbound⟩ := implication_distance_after_arc rep G root a b n hd hab
      have hlow := literal_score_candidate_lower rep G F δ root b m hf hm
      have hcast : (m : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hbound
      have hnum : δ root - n ≤ δ root - m + 1 := by linarith
      have hlow' : ((δ root - n : ℝ) : WithBot ℝ) ≤ ((δ root - m + 1 : ℝ) : WithBot ℝ) := by
        exact_mod_cast hnum
      have hadd := add_le_add_right hlow ((1 : ℝ) : WithBot ℝ)
      have hlow'' : ((δ root - m + 1 : ℝ) : WithBot ℝ) ≤
          literalScore rep G F δ b + ((1 : ℝ) : WithBot ℝ) := by
        simpa only [← WithBot.coe_add, add_comm] using hadd
      simp only [hf, ↓reduceIte, hd]
      exact hlow'.trans hlow''
  · simp [hf]
