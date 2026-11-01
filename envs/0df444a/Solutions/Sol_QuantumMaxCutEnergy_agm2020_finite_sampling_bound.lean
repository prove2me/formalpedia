-- Prove2me | solution 1 for QuantumMaxCutEnergy.agm2020_finite_sampling_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-01T01:00:56.487926+00:00
-- url     : https://prove2.me/submissions/614396c1-f3cd-4298-8fb7-95d6c45956cf

import Mathlib

theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (X : Ω → ℝ) (W m : ℝ)
    (hW : 0 ≤ W) (hm : 0 ≤ m) (hmW : m ≤ W)
    (hX : ∀ ω, 0 ≤ X ω ∧ X ω ≤ 2 * W)
    (hmean : 3 * m / 2 + W / 2 ≤ (∑ ω, X ω) / (Fintype.card Ω : ℝ)) :
    (1 / 151 : ℝ) ≤
      ((Finset.univ.filter (fun ω => 3 * m / 2 + 0.49 * W ≤ X ω)).card : ℝ) /
        (Fintype.card Ω : ℝ) := by
  classical
  have hN : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  by_cases hz : W = 0
  · have hmz : m = 0 := le_antisymm (by simpa [hz] using hmW) hm
    have hfull : Finset.univ.filter (fun ω => 3 * m / 2 + 0.49 * W ≤ X ω) =
        (Finset.univ : Finset Ω) := by
      ext ω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hz, hmz] using (hX ω).1
    rw [hfull]
    simp only [Finset.card_univ, div_self (ne_of_gt hN)]
    norm_num
  · have hWp : 0 < W := lt_of_le_of_ne hW (Ne.symm hz)
    let t : ℝ := 3 * m / 2 + 0.49 * W
    let S : Finset Ω := Finset.univ.filter (fun ω => t ≤ X ω)
    have hpoint (ω : Ω) :
        X ω ≤ t + if t ≤ X ω then (1.51 : ℝ) * W else 0 := by
      by_cases ht : t ≤ X ω
      · rw [if_pos ht]
        have hu := (hX ω).2
        dsimp [t]
        linarith
      · rw [if_neg ht, add_zero]
        exact le_of_lt (lt_of_not_ge ht)
    have hcount :
        (∑ ω : Ω, if t ≤ X ω then (1.51 : ℝ) * W else 0) =
          (S.card : ℝ) * ((1.51 : ℝ) * W) := by
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rfl
    have hsum : (∑ ω, X ω) ≤
        (Fintype.card Ω : ℝ) * t + (S.card : ℝ) * ((1.51 : ℝ) * W) := by
      calc
        _ ≤ ∑ ω : Ω, (t + if t ≤ X ω then (1.51 : ℝ) * W else 0) :=
          Finset.sum_le_sum (fun ω _ => hpoint ω)
        _ = _ := by
          rw [Finset.sum_add_distrib, hcount]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hmean' := (le_div_iff₀ hN).mp hmean
    have hproduct : (Fintype.card Ω : ℝ) * W ≤ 151 * (S.card : ℝ) * W := by
      dsimp [t] at hsum
      nlinarith
    have hcard : (Fintype.card Ω : ℝ) ≤ 151 * (S.card : ℝ) :=
      le_of_mul_le_mul_right hproduct hWp
    change (1 / 151 : ℝ) ≤ (S.card : ℝ) / (Fintype.card Ω : ℝ)
    apply (le_div_iff₀ hN).2
    linarith

#print axioms solution
