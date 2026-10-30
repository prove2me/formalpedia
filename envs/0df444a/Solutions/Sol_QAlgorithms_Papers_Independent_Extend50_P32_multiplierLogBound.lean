-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P32.multiplierLogBound
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T10:24:02.694193+00:00
-- url     : https://prove2.me/submissions/171e6576-84e6-4f97-84c6-206524703046

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P32
open QAlgorithms.Papers.Independent.Extend50.P32

theorem solution {d : ℕ} (hd : 0 < d) (alpha : Fin d → ℝ)
    (hSorted : Antitone alpha) (hPositive : ∀ i, 0 < alpha i) :
    (∑ j : Fin (d - 1), adjacentProbabilityMultiplier alpha j) ≤
      min (d : ℝ) (Real.log (alpha ⟨0, hd⟩ / alpha ⟨d - 1, by omega⟩)) := by
  have hterm : ∀ j : Fin (d - 1), adjacentProbabilityMultiplier alpha j ≤
      Real.log (alpha ⟨j.val, by omega⟩) - Real.log (alpha ⟨j.val + 1, by omega⟩) := by
    intro j
    have h0 := hPositive ⟨j.val, by omega⟩
    have h1 := hPositive ⟨j.val + 1, by omega⟩
    have hy : 0 < alpha ⟨j.val + 1, by omega⟩ / alpha ⟨j.val, by omega⟩ := div_pos h1 h0
    have := Real.log_le_sub_one_of_pos hy
    rw [Real.log_div h1.ne' h0.ne'] at this
    unfold adjacentProbabilityMultiplier
    have e : (alpha ⟨j.val, by omega⟩ - alpha ⟨j.val + 1, by omega⟩) / alpha ⟨j.val, by omega⟩
        = 1 - alpha ⟨j.val + 1, by omega⟩ / alpha ⟨j.val, by omega⟩ := by
      field_simp
    rw [e]; linarith
  have hle1 : ∀ j : Fin (d - 1), adjacentProbabilityMultiplier alpha j ≤ 1 := by
    intro j
    have h0 := hPositive ⟨j.val, by omega⟩
    have h1 := hPositive ⟨j.val + 1, by omega⟩
    unfold adjacentProbabilityMultiplier
    rw [div_le_one h0]
    linarith
  apply le_min
  · calc (∑ j : Fin (d - 1), adjacentProbabilityMultiplier alpha j)
        ≤ ∑ _j : Fin (d - 1), (1 : ℝ) := Finset.sum_le_sum fun j _ => hle1 j
      _ = ((d - 1 : ℕ) : ℝ) := by simp
      _ ≤ d := by exact_mod_cast Nat.sub_le d 1
  · set g : ℕ → ℝ := fun n => if h : n < d then Real.log (alpha ⟨n, h⟩) else 0 with hg
    have hgv : ∀ n (h : n < d), g n = Real.log (alpha ⟨n, h⟩) := fun n h => by simp [hg, h]
    have htel : (∑ j : Fin (d - 1),
        (Real.log (alpha ⟨j.val, by omega⟩) - Real.log (alpha ⟨j.val + 1, by omega⟩))) =
        g 0 - g (d - 1) := by
      have : ∀ j : Fin (d - 1),
          (Real.log (alpha ⟨j.val, by omega⟩) - Real.log (alpha ⟨j.val + 1, by omega⟩)) =
          g j.val - g (j.val + 1) := by
        intro j
        rw [hgv j.val (by omega), hgv (j.val + 1) (by omega)]
      rw [Finset.sum_congr rfl fun j _ => this j, Fin.sum_univ_eq_sum_range (fun n => g n - g (n + 1)),
        Finset.sum_range_sub']
    calc (∑ j : Fin (d - 1), adjacentProbabilityMultiplier alpha j)
        ≤ ∑ j : Fin (d - 1),
          (Real.log (alpha ⟨j.val, by omega⟩) - Real.log (alpha ⟨j.val + 1, by omega⟩)) :=
          Finset.sum_le_sum fun j _ => hterm j
      _ = g 0 - g (d - 1) := htel
      _ = Real.log (alpha ⟨0, hd⟩ / alpha ⟨d - 1, by omega⟩) := by
        rw [hgv 0 hd, hgv (d - 1) (by omega),
          Real.log_div (hPositive _).ne' (hPositive _).ne']
