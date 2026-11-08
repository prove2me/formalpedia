-- Prove2me | solution 1 for WildeQIT.Hashing.property_14_3_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T21:34:42.414909+00:00
-- url     : https://prove2.me/submissions/a440ce68-06ca-460a-ba78-e3dfe5875b1e

import Definitions.Def_WildeQIT_typicalSet
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open WildeQIT in
theorem solution {α : Type} [Fintype α] (p : FinDist α) (δ : ℝ) (hδ : 0 < δ) (n : ℕ)
    (x : Fin n → α) (hx : x ∈ typicalSet p n δ) :
    (2 : ℝ) ^ (-((n : ℝ) * (entropy p + δ))) ≤ (p.iid n).prob x ∧
      (p.iid n).prob x ≤ (2 : ℝ) ^ (-((n : ℝ) * (entropy p - δ))) := by
  rw [mem_typicalSet] at hx
  obtain ⟨hP, hab⟩ := hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnr : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    unfold sampleEntropy at hab
    obtain ⟨P, hPdef⟩ : ∃ P, P = (p.iid n).prob x := ⟨_, rfl⟩
    rw [← hPdef] at hab hP ⊢
    obtain ⟨L, hLdef⟩ : ∃ L, L = Real.logb 2 P := ⟨_, rfl⟩
    have hPe : (2 : ℝ) ^ L = P := by
      rw [hLdef]; exact Real.rpow_logb (by norm_num) (by norm_num) hP
    rw [← hLdef] at hab
    rw [abs_le] at hab
    obtain ⟨hl, hr⟩ := hab
    have e : (n : ℝ) * (-(1 / (n : ℝ)) * L) = -L := by
      rw [← mul_assoc, mul_neg, mul_one_div_cancel hnr.ne', neg_one_mul]
    have h3 : (n : ℝ) * (-(1 / (n : ℝ)) * L - entropy p) ≤ n * δ :=
      mul_le_mul_of_nonneg_left hr hnr.le
    have h4 : (n : ℝ) * (-δ) ≤ n * (-(1 / (n : ℝ)) * L - entropy p) :=
      mul_le_mul_of_nonneg_left hl hnr.le
    rw [mul_sub, e] at h3 h4
    constructor
    · rw [← hPe]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    · rw [← hPe]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
