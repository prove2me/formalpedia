-- Prove2me | solution 1 for RobustPower.StochGap.Supplement.theorem_4_4_simplex_adapt_gap
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-24T03:10:09.580666+00:00
-- url     : https://prove2.me/submissions/c08c5b63-f481-4df3-9c5a-b391a14fd756

import Mathlib
import Definitions.Def_RobustPower_StochGap_Problems
import Definitions.Def_RobustPower_AdaptGap_Problems
import Definitions.Def_RobustPower_SimplexGap_SimplexInstance

open Matrix
namespace RobustPower.StochGap.Supplement

theorem theorem_4_4_simplex_adapt_gap {n : ℕ} (hn : 3 ≤ n) {Ω : Type*}
    (b : Ω → Fin n → ℝ)
    (hrange : Set.range b = RobustPower.SimplexGap.cornerSimplex n) :
    ((n : ℝ) : EReal) * RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin n) (Fin 0) ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) b 0 (fun _ _ => 1) ∅ ∅ ≤
      RobustPower.StochGap.zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)
        b ∅ ∅ 0 (fun _ => 1) := by
  have hr : ∀ ω, ∑ j, b ω j ≤ 1 ∧ 0 ≤ b ω := fun ω => by
    have h : b ω ∈ Set.range b := ⟨ω, rfl⟩
    rw [hrange] at h; exact h
  have hc : ∀ j : Fin n, ∃ ω, b ω = Pi.single j 1 := fun j => by
    have h : (Pi.single j 1 : Fin n → ℝ) ∈ RobustPower.SimplexGap.cornerSimplex n := by
      refine ⟨by simp, Pi.single_nonneg.mpr zero_le_one⟩
    rw [← hrange] at h; exact h
  have h1 : ((1:ℝ):EReal) = 1 := rfl
  have hzr : ((n : ℝ) : EReal) ≤ RobustPower.StochGap.zRob (0 : Matrix (Fin n) (Fin 0) ℝ)
      (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ 0 (fun _ => 1) := by
    unfold RobustPower.StochGap.zRob
    refine le_iInf fun x => le_iInf fun y => le_iInf fun hf => ?_
    obtain ⟨_, _, hb⟩ := hf
    have hy : ∀ j, 1 ≤ y j := fun j => by
      obtain ⟨ω, hω⟩ := hc j
      have e := hb ω j
      rw [hω] at e
      simpa using e
    have : (n : ℝ) ≤ (0 : Fin 0 → ℝ) ⬝ᵥ x + (fun _ : Fin n => (1:ℝ)) ⬝ᵥ y := by
      rw [show (0 : Fin 0 → ℝ) ⬝ᵥ x = 0 from by simp [dotProduct], zero_add]; simp only [dotProduct, one_mul]
      calc (n : ℝ) = ∑ _j : Fin n, (1:ℝ) := by simp
        _ ≤ ∑ j, y j := Finset.sum_le_sum fun j _ => hy j
    exact EReal.coe_le_coe_iff.mpr this
  have hza : RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin n) (Fin 0) ℝ)
      (1 : Matrix (Fin n) (Fin n) ℝ) b 0 (fun _ _ => 1) ∅ ∅ ≤ 1 := by
    unfold RobustPower.AdaptGap.zAdapt RobustPower.AdaptGap.adaptCost
    have hf : RobustPower.AdaptGap.AdaptFeasible (0 : Matrix (Fin n) (Fin 0) ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) b ∅ ∅ 0 b :=
      ⟨⟨le_refl _, by simp⟩, fun ω => ⟨⟨(hr ω).2, by simp⟩, by simp⟩⟩
    refine iInf_le_of_le 0 (iInf_le_of_le b (iInf_le_of_le hf ?_))
    simp only [dotProduct_zero, EReal.coe_zero, zero_add]
    refine iSup_le fun ω => ?_
    have : (fun _ : Fin n => (1:ℝ)) ⬝ᵥ b ω ≤ 1 := by
      simp only [dotProduct, one_mul]; exact (hr ω).1
    rw [← h1]; exact EReal.coe_le_coe_iff.mpr this
  have hn0 : (0 : EReal) ≤ ((n : ℝ) : EReal) := EReal.coe_nonneg.mpr (Nat.cast_nonneg n)
  calc ((n : ℝ) : EReal) * _ ≤ ((n : ℝ) : EReal) * 1 := mul_le_mul_of_nonneg_left hza hn0
    _ = ((n : ℝ) : EReal) := mul_one _
    _ ≤ _ := hzr

end RobustPower.StochGap.Supplement

open RobustPower.StochGap.Supplement in
theorem solution {n : ℕ} (hn : 3 ≤ n) {Ω : Type*}
    (b : Ω → Fin n → ℝ)
    (hrange : Set.range b = RobustPower.SimplexGap.cornerSimplex n) :
    ((n : ℝ) : EReal) * RobustPower.AdaptGap.zAdapt (0 : Matrix (Fin n) (Fin 0) ℝ)
        (1 : Matrix (Fin n) (Fin n) ℝ) b 0 (fun _ _ => 1) ∅ ∅ ≤
      RobustPower.StochGap.zRob (0 : Matrix (Fin n) (Fin 0) ℝ) (1 : Matrix (Fin n) (Fin n) ℝ)
        b ∅ ∅ 0 (fun _ => 1) :=
  RobustPower.StochGap.Supplement.theorem_4_4_simplex_adapt_gap hn b hrange
