-- Prove2me | solution 1 for RH.Transport.SupportedMass.weighted_mass_decay
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T22:49:58.191674+00:00
-- url     : https://prove2.me/submissions/2953109d-4bac-404e-8834-fc6bfa634716

import Definitions.Def_Transport_Geometry
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Ring.Finset
import Definitions.Def_Transport_SupportedMass
set_option autoImplicit false
open RH RH.Transport RH.Transport.SupportedMass
open scoped BigOperators Classical
noncomputable section

theorem solution {ι : Type*} (F : Finset ι)
    (q w : ι → ℝ) {a Z C ell : ℝ}
    (ha : 0 < a) (hZ : 0 < Z)
    (hw : ∀ i ∈ F, 0 ≤ w i)
    (hsupport : ∀ i ∈ F, w i ≠ 0 → a * Z ^ ell ≤ q i)
    (hmass : (∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ))) ≤ C) :
    (∑ i ∈ F, w i * q i ^ (-2 : ℝ)) ≤
      (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by
  have hT : 0 < a * Z ^ ell := mul_pos ha (Real.rpow_pos_of_pos hZ _)
  have hid : (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) =
      a ^ (-(1 / 2 : ℝ)) * Z ^ (-ell / 2) := by
    rw [Real.mul_rpow ha.le (Real.rpow_nonneg hZ.le _), ← Real.rpow_mul hZ.le]
    congr 2
    ring
  have hterm : ∀ i ∈ F, w i * q i ^ (-2 : ℝ) ≤
      (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) * (w i * q i ^ (-(3 / 2 : ℝ))) := by
    intro i hi
    by_cases h0 : w i = 0
    · simp [h0]
    · have hq := hsupport i hi h0
      have hq0 : 0 < q i := lt_of_lt_of_le hT hq
      have h1 : q i ^ (-(1 / 2 : ℝ)) ≤ (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hT hq (by norm_num)
      have h2 : q i ^ (-2 : ℝ) = q i ^ (-(1 / 2 : ℝ)) * q i ^ (-(3 / 2 : ℝ)) := by
        rw [← Real.rpow_add hq0]; norm_num
      rw [h2]
      have := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hq0.le (-(3 / 2 : ℝ)))
      have := mul_le_mul_of_nonneg_left this (hw i hi)
      linarith
  calc (∑ i ∈ F, w i * q i ^ (-2 : ℝ))
      ≤ ∑ i ∈ F, (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) * (w i * q i ^ (-(3 / 2 : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) * ∑ i ∈ F, w i * q i ^ (-(3 / 2 : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (a * Z ^ ell) ^ (-(1 / 2 : ℝ)) * C :=
        mul_le_mul_of_nonneg_left hmass (Real.rpow_nonneg hT.le _)
    _ = (C * a ^ (-(1 / 2 : ℝ))) * Z ^ (-ell / 2) := by
        rw [hid]; ring
