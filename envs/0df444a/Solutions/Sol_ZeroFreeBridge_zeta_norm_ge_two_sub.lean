-- Prove2me | solution 1 for ZeroFreeBridge.zeta_norm_ge_two_sub
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-28T07:56:38.859836+00:00
-- url     : https://prove2.me/submissions/84115f68-5e64-4bb8-a59d-999d933c0ca1

import Mathlib
import Theorems.Thm_ZeroFreeBridge_basel_tail

/- PHASE 4 (dVP frontier, ζ boundary growth — LOWER BOUND): a uniform lower bound on |ζ|
   at Re s = 2, the missing lower half of the ζ-growth sphere input.

   The composition `DlvpBoundaryDecomp.norm_logDeriv_le_of_boundary_split` needs, on the sphere,
   `log‖ζ z‖ - log‖ζ c‖ ≤ Aζ`; the upper half is `zeta_sphere_bound`, the lower half is a POSITIVE
   lower bound `‖ζ c‖ ≥ c₀`.  Centering the dVP disk at `Re c = 2` makes this an absolute constant:

     `2 - π²/6 ≤ ‖ζ(s)‖`   for   `2 ≤ Re s`   (and `2 - π²/6 > 0`).

   Proof: `ζ(s) = ∑ₙ 1/(n+1)^s = 1 + T` (Dirichlet series, `n=0` term is `1`); reverse triangle
   `‖ζ‖ ≥ 1 - ‖T‖`; `‖T‖ ≤ ∑ₙ 1/(n+2)^{Re s} ≤ ∑ₙ 1/(n+2)² = π²/6 - 1` (termwise since `Re s ≥ 2`,
   the tail of Basel `hasSum_zeta_two`); so `‖ζ‖ ≥ 1 - (π²/6 - 1) = 2 - π²/6`.  conjecture1_proved = False.
-/


open Complex

section
namespace ZeroFreeBridge
end ZeroFreeBridge
open ZeroFreeBridge




theorem solution {s : ℂ} (hs : 2 ≤ s.re) :
    2 - Real.pi ^ 2 / 6 ≤ ‖riemannZeta s‖ := by
  have h1 : (1 : ℝ) < s.re := by linarith
  have hzeta : riemannZeta s = ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ s :=
    zeta_eq_tsum_one_div_nat_add_one_cpow h1
  set f : ℕ → ℂ := fun n => 1 / ((n : ℂ) + 1) ^ s with hf
  have hsum_c : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr h1
  have hsumf : Summable f := by
    have h := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℂ) ^ s) 1).mpr hsum_c
    simpa [hf, Nat.cast_add, Nat.cast_one] using h
  have hsplit : riemannZeta s = f 0 + ∑' n : ℕ, f (n + 1) := by
    rw [hzeta]; exact hsumf.tsum_eq_zero_add
  have hf0 : f 0 = 1 := by simp [hf]
  set T : ℂ := ∑' n : ℕ, f (n + 1) with hT
  -- reverse triangle: ‖ζ‖ ≥ 1 - ‖T‖
  have hrev : (1 : ℝ) - ‖T‖ ≤ ‖riemannZeta s‖ := by
    have heq : (1 : ℂ) = riemannZeta s - T := by rw [hsplit, hf0]; ring
    have hsub : ‖(1 : ℂ)‖ ≤ ‖riemannZeta s‖ + ‖T‖ := by rw [heq]; exact norm_sub_le _ _
    rw [norm_one] at hsub; linarith
  -- ‖f (n+1)‖ = 1/(n+2)^{Re s}
  have hnorm_term : ∀ n : ℕ, ‖f (n + 1)‖ = 1 / (((n : ℝ) + 2)) ^ s.re := by
    intro n
    have hpos : 0 < ((n : ℕ) + 2) := by positivity
    rw [hf]
    simp only [Nat.cast_add, Nat.cast_one]
    rw [norm_div, norm_one]
    have hc : ((n : ℂ) + 1 + 1) = ((n + 2 : ℕ) : ℂ) := by push_cast; ring
    rw [hc, norm_natCast_cpow_of_pos hpos]
    push_cast; ring_nf
  have hsummf1 : Summable (fun n : ℕ => ‖f (n + 1)‖) :=
    (hsumf.comp_injective (add_left_injective 1)).norm
  have hTle : ‖T‖ ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re := by
    calc ‖T‖ = ‖∑' n : ℕ, f (n + 1)‖ := by rw [hT]
      _ ≤ ∑' n : ℕ, ‖f (n + 1)‖ := norm_tsum_le_tsum_norm hsummf1
      _ = ∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re := tsum_congr hnorm_term
  -- termwise: 1/(n+2)^{Re s} ≤ 1/(n+2)²  since Re s ≥ 2 and n+2 ≥ 1
  have hbase : ∀ n : ℕ, (1 : ℝ) ≤ (n : ℝ) + 2 := by
    intro n; have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n; linarith
  have hmono : ∀ n : ℕ, (1 : ℝ) / (((n : ℝ) + 2)) ^ s.re ≤ 1 / (((n : ℝ) + 2)) ^ 2 := by
    intro n
    have hpow : (((n : ℝ) + 2)) ^ (2 : ℝ) ≤ (((n : ℝ) + 2)) ^ s.re :=
      Real.rpow_le_rpow_of_exponent_le (hbase n) hs
    rw [Real.rpow_two] at hpow
    exact one_div_le_one_div_of_le (by positivity) hpow
  have hsumσ : Summable (fun n : ℕ => 1 / (((n : ℝ) + 2)) ^ s.re) := by
    simpa only [hnorm_term] using hsummf1
  have hsum2 : Summable (fun n : ℕ => 1 / (((n : ℝ) + 2)) ^ 2) := by
    have hz := hasSum_zeta_two.summable
    have h2 := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) 2).mpr hz
    refine h2.congr (fun n => ?_); push_cast; ring_nf
  have htail : (∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re) ≤ Real.pi ^ 2 / 6 - 1 := by
    calc (∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ s.re)
        ≤ ∑' n : ℕ, 1 / (((n : ℝ) + 2)) ^ 2 := Summable.tsum_le_tsum hmono hsumσ hsum2
      _ = Real.pi ^ 2 / 6 - 1 := basel_tail
  linarith [hrev, le_trans hTle htail]
