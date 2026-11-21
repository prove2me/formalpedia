-- Prove2me | solution 2 for RiemannMasullo.additiveCharacter_proportional_of_slab
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-20T23:09:54.100107+00:00
-- url     : https://prove2.me/submissions/fc26036c-358d-4c3f-b102-65639e416be4

import Mathlib

/-- Two real additive characters are proportional if the second is bounded on a
    thick enough slab of the first. The integer part keeps each multiple in the slab. -/
theorem solution {G : Type*} [AddCommGroup G] (a b : G →+ ℝ) (u : G)
    (hu : 0 < a u) (C : ℝ) (hC : ∀ x, 0 ≤ a x → a x ≤ a u → |b x| ≤ C) (x : G) :
    b x = a x * (b u / a u) := by
  let s := b u / a u
  have hus : a u * s = b u := by dsimp [s]; field_simp
  have hbound (n : ℕ) : (n : ℝ) * |b x - a x * s| ≤ C + a u * |s| := by
    let k : ℤ := ⌊(n : ℝ) * a x / a u⌋
    let y := n • x - k • u
    have hka : (k : ℝ) * a u ≤ (n : ℝ) * a x :=
      (le_div_iff₀ hu).mp (Int.floor_le _)
    have hkb : (n : ℝ) * a x < ((k : ℝ) + 1) * a u :=
      (div_lt_iff₀ hu).mp (Int.lt_floor_add_one _)
    have hay : a y = (n : ℝ) * a x - (k : ℝ) * a u := by simp [y]
    have hby : b y = (n : ℝ) * b x - (k : ℝ) * b u := by simp [y]
    have hy0 : 0 ≤ a y := by rw [hay]; linarith
    have hy1 : a y ≤ a u := by rw [hay]; linarith
    have he : (n : ℝ) * (b x - a x * s) = b y - a y * s := by
      rw [hby, hay, ← hus]; ring
    calc
      (n : ℝ) * |b x - a x * s| = |(n : ℝ) * (b x - a x * s)| := by
        simpa only [abs_mul, Nat.abs_cast]
      _ = |b y - a y * s| := congrArg abs he
      _ ≤ |b y| + |a y * s| := abs_sub _ _
      _ ≤ C + a u * |s| := by
        rw [abs_mul, abs_of_nonneg hy0]
        exact add_le_add (hC y hy0 hy1) (mul_le_mul_of_nonneg_right hy1 (abs_nonneg _))
  by_contra h
  have hd : 0 < |b x - a x * s| := abs_pos.mpr (sub_ne_zero.mpr h)
  obtain ⟨n, hn⟩ := exists_nat_gt ((C + a u * |s|) / |b x - a x * s|)
  exact (not_lt_of_ge (hbound n)) ((div_lt_iff₀ hd).mp hn)

