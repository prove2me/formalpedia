-- Prove2me | solution 1 for StabilityDichotomies.Bijunctive.positive_winning_root_dominates_both_literals
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:00:22.962192+00:00
-- url     : https://prove2.me/submissions/8e543181-fc42-4435-8aab-7241367890f0

import Theorems.Thm_StabilityDichotomies_Bijunctive_satisfiable_positive_shift_has_positive_literal_score
import Theorems.Thm_StabilityDichotomies_Bijunctive_positive_score_has_maximizing_root
import Theorems.Thm_StabilityDichotomies_Bijunctive_feasible_root_cannot_reach_opposites
noncomputable section
open scoped Classical BigOperators
open StabilityDichotomies.Solvability StabilityDichotomies.Bijunctive

private theorem distance_walk {Γ : Language} {V : Type} (rep : TwoCNFRepresentation Γ)
    (G : Instance Γ V) (a b : Literal V) (n : ℕ)
    (hd : implicationDistance rep G a b = some n) : WalkLength (implicationArc rep G) n a b := by
  unfold implicationDistance at hd
  split at hd
  next h =>
    have hn : Nat.find h = n := Option.some.inj hd
    simpa [← hn] using Nat.find_spec h
  next h => simp at hd

private theorem candidate_lower {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (δ : Literal V → ℝ)
    (root target : Literal V) (n : ℕ) (hr : feasibleLiteral F root)
    (hd : implicationDistance rep G root target = some n) :
    ((δ root - n : ℝ) : WithBot ℝ) ≤ literalScore rep G F δ target := by
  unfold literalScore
  apply Finset.le_sup_of_le (Finset.mem_univ root)
  simp [hr,hd]

theorem solution {Γ : Language} {V : Type} [Fintype V]
    (rep : TwoCNFRepresentation Γ) (G F : Instance Γ V) (hF : Satisfiable F)
    (hsub : ∀ c ∈ G.constraints, c ∈ F.constraints)
    (δ : Literal V → ℝ) (hδ : ∀ a, 0 < δ a) (v : V) :
    ∃ (root : Literal V) (n : ℕ) (w : Bool),
      w = decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)) ∧
      feasibleLiteral F root ∧ implicationDistance rep G root (v,w) = some n ∧
      literalScore rep G F δ (v,w) = ((δ root - n : ℝ) : WithBot ℝ) ∧
      0 < δ root - n ∧
      (∀ (r : Literal V) (m : ℕ) (z : Bool), feasibleLiteral F r →
        implicationDistance rep G r (v,z) = some m → δ r - m ≤ δ root - n) ∧
      ¬ ∃ m, WalkLength (implicationArc rep G) m root (v,!w) := by
  classical
  let w := decide (literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true))
  have hpos : (0 : WithBot ℝ) < literalScore rep G F δ (v,w) := by
    obtain ⟨z,hz⟩ := satisfiable_positive_shift_has_positive_literal_score rep G F hF δ hδ v
    by_cases h : literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)
    · have hw : w = true := by simp [w,h]
      rw [hw]
      cases z with
      | false => exact hz.trans h
      | true => exact hz
    · have hw : w = false := by simp [w,h]
      rw [hw]
      cases z with
      | false => exact hz
      | true => exact hz.trans_le (le_of_not_gt h)
  obtain ⟨root,n,hroot,hd,heq,hmax⟩ := positive_score_has_maximizing_root rep G F δ (v,w) hpos
  have hnum : 0 < δ root - n := by
    rw [heq] at hpos
    exact_mod_cast hpos
  have hwin (z : Bool) : literalScore rep G F δ (v,z) ≤ literalScore rep G F δ (v,w) := by
    by_cases h : literalScore rep G F δ (v,false) < literalScore rep G F δ (v,true)
    · have hw : w = true := by simp [w,h]
      rw [hw]
      cases z with
      | false => exact le_of_lt h
      | true => exact le_rfl
    · have hw : w = false := by simp [w,h]
      rw [hw]
      cases z with
      | false => exact le_rfl
      | true => exact le_of_not_gt h
  refine ⟨root,n,w,rfl,hroot,hd,heq,hnum,?_,?_⟩
  · intro r m z hr hrD
    have hh := (candidate_lower rep G F δ r (v,z) m hr hrD).trans (hwin z)
    rw [heq] at hh
    exact_mod_cast hh
  · intro hreach
    obtain ⟨m,hm⟩ := hreach
    have hneg : literalNeg (v,w) = (v,!w) := rfl
    have hbad := feasible_root_cannot_reach_opposites rep G F hsub root (v,w) hroot
    exact hbad ⟨n,m,distance_walk rep G root (v,w) n hd,by simpa [hneg] using hm⟩
