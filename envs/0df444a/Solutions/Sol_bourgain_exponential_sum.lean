-- Prove2me | solution 1 for bourgain_exponential_sum
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T08:01:59.176495+00:00
-- url     : https://prove2.me/submissions/89620791-2da5-48c2-aca7-20ed849178ff

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

private theorem interval_term_re (n : ℕ) (hn : n < 600) :
    (1 / 2 : ℝ) ≤ (Complex.exp (2 * Real.pi * Complex.I * n / 4099)).re := by
  have hnR : (n : ℝ) ≤ 600 := by exact_mod_cast (Nat.le_of_lt hn)
  have ht : 0 ≤ 2 * Real.pi * (n : ℝ) / 4099 := by positivity
  have hu : 2 * Real.pi * (n : ℝ) / 4099 ≤ Real.pi / 3 := by
    calc
      _ ≤ 2 * Real.pi * 600 / 4099 := by gcongr
      _ ≤ Real.pi / 3 := by linarith [Real.pi_pos]
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi ht
    (show Real.pi / 3 ≤ Real.pi by linarith [Real.pi_pos]) hu
  rw [Real.cos_pi_div_three] at hc
  have he : (2 * Real.pi * Complex.I * n / 4099 : ℂ) =
      ((2 * Real.pi * (n : ℝ) / 4099 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he, Complex.exp_ofReal_mul_I_re]
  exact hc

private theorem interval_large_enough :
    (4099 : ℝ) ^ (1 / 2 + (1 / 4 : ℝ)) ≤ 600 := by
  apply (Real.rpow_le_rpow_iff (by positivity) (by norm_num)
    (by norm_num : (0 : ℝ) < 4)).mp
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4099)]
  norm_num

private theorem cancellation_factor_small :
    (4099 : ℝ) ^ (-(1 / 4 : ℝ) / 2) < 1 / 2 := by
  have h256 : (256 : ℝ) ^ (-1 / 8 : ℝ) = 1 / 2 := by
    calc
      _ = ((2 : ℝ) ^ (8 : ℕ)) ^ (-1 / 8 : ℝ) := by norm_num
      _ = (2 : ℝ) ^ ((8 : ℝ) * (-1 / 8)) :=
        (Real.rpow_natCast_mul (by norm_num) 8 (-1 / 8)).symm
      _ = 1 / 2 := by norm_num
  have ht : (4099 : ℝ) ^ (-1 / 8 : ℝ) < (256 : ℝ) ^ (-1 / 8 : ℝ) :=
    Real.rpow_lt_rpow_of_neg (by norm_num) (by norm_num) (by norm_num)
  rw [show -(1 / 4 : ℝ) / 2 = -1 / 8 by ring, ← h256]
  exact ht

theorem solution : ¬ (∀ (p : ℕ), Nat.Prime p → ∀ (delta : ℝ),
    (0 < delta ∧ delta < 1 / 2) → ∀ (A : Finset (ZMod p)),
      (p : ℝ) ^ (1 / 2 + delta) ≤ A.card →
      ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * a.val / p)‖ ≤
        (A.card : ℝ) * (p : ℝ) ^ (-delta / 2)) := by
  classical
  intro h
  let A : Finset (ZMod 4099) := (Finset.range 600).image (fun n : ℕ => (n : ZMod 4099))
  have hval (n : ℕ) (hn : n < 600) : (n : ZMod 4099).val = n :=
    ZMod.val_natCast_of_lt (by omega)
  have hinj : Set.InjOn (fun n : ℕ => (n : ZMod 4099)) (Finset.range 600) := by
    intro n hn m hm he
    have hh := congrArg ZMod.val he
    rwa [hval n (Finset.mem_range.mp hn), hval m (Finset.mem_range.mp hm)] at hh
  have hcard : A.card = 600 := by
    dsimp [A]
    rw [Finset.card_image_iff.mpr hinj, Finset.card_range]
  have hmem (a : ZMod 4099) (ha : a ∈ A) : a.val < 600 := by
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    rw [hval n (Finset.mem_range.mp hn)]
    exact Finset.mem_range.mp hn
  have hsum : (300 : ℝ) ≤
      (∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * a.val / 4099)).re := by
    calc
      (300 : ℝ) = ∑ _a ∈ A, (1 / 2 : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, hcard]
        norm_num
      _ ≤ ∑ a ∈ A, (Complex.exp (2 * Real.pi * Complex.I * a.val / 4099)).re :=
        Finset.sum_le_sum (fun a ha => interval_term_re a.val (hmem a ha))
      _ = _ := by simp
  have hlow := hsum.trans (Complex.re_le_norm _)
  have hu := h 4099 (by norm_num) (1 / 4) (by norm_num) A
    (by rw [hcard]; exact interval_large_enough)
  rw [hcard] at hu
  have hsmall : (600 : ℝ) * (4099 : ℝ) ^ (-(1 / 4 : ℝ) / 2) < 300 := by
    linarith [cancellation_factor_small]
  exact (not_lt_of_ge hlow) (hu.trans_lt hsmall)

#print axioms solution
