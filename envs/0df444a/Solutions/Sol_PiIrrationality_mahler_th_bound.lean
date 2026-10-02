-- Prove2me | solution 1 for PiIrrationality.mahler_th_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-02T10:32:50.824951+00:00
-- url     : https://prove2.me/submissions/441732eb-a403-4153-880d-8ac2fe3f5db5

import Mathlib

theorem solution (m : ℕ) (hm : 2 ≤ m)
    (A : ℕ → ℕ → ℂ → ℂ)
    (ψ : ℕ → ℕ → ℂ → ℂ)
    (Th : ℕ → ℂ → ℂ → ℂ)
    (hTh : ∀ h x y, h ≤ m →
      Th h x y = Finset.sum (Finset.range m) (fun k => A h k x * ψ h k y))
    (hψ : ∀ h k y, h ≤ m → k < m → ‖y‖ < 2 →
      ‖ψ h k y‖ < 2 ^ m)
    (maxA : ℝ) (hmaxA : 0 < maxA)
    (hbound : ∀ h k x, h ≤ m → k ≤ m →
      ‖Complex.log x‖ < 2 → ‖A h k x‖ ≤ maxA)
    (x y : ℂ) (h : ℕ) (hh : h ≤ m)
    (hlog : ‖Complex.log x‖ < 2)
    (hy : ‖y‖ < 2) :
    ‖Th h x y‖ < 2 ^ m * (m : ℝ) * maxA := by
  rw [hTh h x y hh]
  have hne : (Finset.range m).Nonempty := ⟨0, Finset.mem_range.mpr (by omega)⟩
  calc ‖∑ k ∈ Finset.range m, A h k x * ψ h k y‖
      ≤ ∑ k ∈ Finset.range m, ‖A h k x * ψ h k y‖ := norm_sum_le _ _
    _ < ∑ k ∈ Finset.range m, maxA * 2 ^ m := by
        apply Finset.sum_lt_sum_of_nonempty hne
        intro k hk
        have hk' : k < m := Finset.mem_range.mp hk
        rw [norm_mul]
        have h1 := hbound h k x hh hk'.le hlog
        have h2 := hψ h k y hh hk' hy
        have h3 : 0 ≤ ‖ψ h k y‖ := norm_nonneg _
        calc ‖A h k x‖ * ‖ψ h k y‖ ≤ maxA * ‖ψ h k y‖ :=
              mul_le_mul_of_nonneg_right h1 h3
          _ < maxA * 2 ^ m := mul_lt_mul_of_pos_left h2 hmaxA
    _ = 2 ^ m * (m : ℝ) * maxA := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
