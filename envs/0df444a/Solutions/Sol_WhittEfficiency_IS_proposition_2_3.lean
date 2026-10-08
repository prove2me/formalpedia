-- Prove2me | solution 1 for WhittEfficiency.IS.proposition_2_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T18:50:02.371114+00:00
-- url     : https://prove2.me/submissions/7471a169-8501-413c-b665-bfbc4bf025d4

import Mathlib
import Definitions.Def_WhittEfficiency_IS_Model

open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations
open WhittEfficiency.IS

theorem solution {Ω : Type*} (T : ℕ → Ω → ℝ) (ω : Ω) (t : ℝ)
    (hpos : ∀ i, 0 < T i ω)
    (hfin : {n : ℕ | 1 ≤ n ∧ arrivalTime T n ω ≤ t}.Finite) :
    (busyCount T (fun _ _ => 1) t ω : ℤ) = countingProcess T t ω - countingProcess T (t - 1) ω := by
  classical
  let S : Set ℕ := {n | 1 ≤ n ∧ arrivalTime T n ω ≤ t}
  let R : Set ℕ := {n | 1 ≤ n ∧ arrivalTime T n ω ≤ t - 1}
  let B : Set ℕ := {k | arrivalTime T (k + 1) ω ≤ t ∧ t < arrivalTime T (k + 1) ω + 1}
  have hRS : R ⊆ S := by
    intro n hn
    exact ⟨hn.1, by linarith [hn.2]⟩
  have hBR : Nat.succ '' B = S \ R := by
    ext n
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨by omega, hk.1⟩, fun hn => by dsimp [R] at hn; dsimp [B] at hk; linarith [hn.2, hk.2]⟩
    · rintro ⟨hn, hr⟩
      refine ⟨n - 1, ?_, by dsimp [S] at hn; omega⟩
      have he : n - 1 + 1 = n := by dsimp [S] at hn; omega
      dsimp [B]
      rw [he]
      refine ⟨hn.2, ?_⟩
      have hnt : ¬ arrivalTime T n ω ≤ t - 1 := fun h => hr ⟨hn.1, h⟩
      linarith
  have hc : B.ncard = (S \ R).ncard := by
    rw [← hBR, Set.ncard_image_of_injective B Nat.succ_injective]
  have hadd := Set.ncard_sdiff_add_ncard_of_subset hRS hfin
  change (B.ncard : ℤ) = (S.ncard : ℤ) - (R.ncard : ℤ)
  rw [hc]
  have hi : ((S \ R).ncard : ℤ) + (R.ncard : ℤ) = (S.ncard : ℤ) := by
    exact_mod_cast hadd
  omega

#print axioms solution
