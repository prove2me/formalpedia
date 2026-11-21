-- Prove2me | solution 1 for RiemannMasullo.additiveCharacter_proportional_of_slab
-- status  : ACCEPTED   (prove)
-- author  : @nlehmann
-- created : 2026-11-20T22:58:11.589012+00:00
-- url     : https://prove2.me/submissions/0f16f99e-fbcc-41f7-bc42-e21cacd7a7ab

import Mathlib

theorem solution {G : Type*} [AddCommGroup G] (a b : G →+ ℝ) (u : G)
    (hu : 0 < a u) (C : ℝ) (hC : ∀ x, 0 ≤ a x → a x ≤ a u → |b x| ≤ C) (x : G) :
    b x = a x * (b u / a u) := by
  set c := b u / a u with hc
  set D := b x - c * a x with hD
  -- uniform bound on m * D
  have hbound : ∀ m : ℕ, |(m : ℝ) * D| ≤ C + |c| * a u := by
    intro m
    set k : ℤ := ⌊(m : ℝ) * a x / a u⌋ with hk
    set y : G := m • x - k • u with hy
    have hay : a y = m * a x - k * a u := by
      simp [hy, map_sub, map_nsmul, map_zsmul, nsmul_eq_mul, zsmul_eq_mul]
    have hby : b y = m * b x - k * b u := by
      simp [hy, map_sub, map_nsmul, map_zsmul, nsmul_eq_mul, zsmul_eq_mul]
    have hfl1 : (k : ℝ) ≤ m * a x / a u := Int.floor_le _
    have hfl2 : m * a x / a u < k + 1 := Int.lt_floor_add_one _
    have h0 : 0 ≤ a y := by
      rw [hay]
      have := (le_div_iff₀ hu).1 hfl1
      linarith
    have h1 : a y ≤ a u := by
      rw [hay]
      have := (div_lt_iff₀ hu).1 hfl2
      nlinarith
    have hbyC := hC y h0 h1
    have hdy : (m : ℝ) * D = b y - c * a y := by
      rw [hby, hay, hD, hc]
      field_simp
      ring
    rw [hdy]
    calc |b y - c * a y| ≤ |b y| + |c * a y| := abs_sub _ _
      _ ≤ C + |c| * a u := by
        rw [abs_mul]
        gcongr
        rw [abs_of_nonneg h0]; exact h1
  -- conclude D = 0
  have hD0 : D = 0 := by
    by_contra hne
    have hpos : 0 < |D| := abs_pos.2 hne
    obtain ⟨m, hm⟩ := exists_nat_gt ((C + |c| * a u) / |D|)
    have := hbound m
    rw [abs_mul, Nat.abs_cast] at this
    have := (div_lt_iff₀ hpos).1 hm
    linarith
  have : b x = c * a x := by linarith
  rw [this, mul_comm]
