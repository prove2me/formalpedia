-- Prove2me | solution 1 for ShockWear.Inherit.hazard_bound25
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:09:10.813536+00:00
-- url     : https://prove2.me/submissions/712a9c50-b455-4e83-856b-d2c37fe4de46

import Mathlib
import Definitions.Def_ShockWear_Inherit_Model
open ShockWear.Inherit ShockWear.CumDamage

theorem solution (lam : ℝ) (hlam : 0 < lam) (P : ℕ → ℝ)
    (hP0 : P 0 ≤ 1) (hanti : Antitone P) (hnn : ∀ k, 0 ≤ P k) :
    ∀ t, 0 < t → shockDens lam P t ≤ lam * ShockWear.CumDamage.shockSurv lam P t := by
  intro t ht
  have hw (k : ℕ) : 0 ≤ poisW lam t k := by unfold poisW; positivity
  have hs : Summable (poisW lam t) := by
    change Summable (fun k => Real.exp (-(lam * t)) * (lam * t) ^ k / (k.factorial : ℝ))
    simpa only [poisW, ← mul_div_assoc] using
      (Real.summable_pow_div_factorial (lam * t)).mul_left (Real.exp (-(lam * t)))
  have hPk (k : ℕ) : P k ≤ 1 := (hanti (Nat.zero_le k)).trans hP0
  have hp : Summable (fun k => P k * poisW lam t k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hnn k) (hw k))
      (fun k => by simpa using mul_le_mul_of_nonneg_right (hPk k) (hw k)) hs
  have hf0 (k : ℕ) : 0 ≤ failProb P (k + 1) := by
    simp only [failProb]
    exact sub_nonneg.mpr (hanti (Nat.le_succ k))
  have hfle (k : ℕ) : failProb P (k + 1) * poisW lam t k ≤ P k * poisW lam t k := by
    apply mul_le_mul_of_nonneg_right _ (hw k)
    simp only [failProb]
    linarith [hnn (k + 1)]
  have hf := Summable.of_nonneg_of_le (fun k => mul_nonneg (hf0 k) (hw k)) hfle hp
  unfold shockDens shockSurv
  rw [if_neg (by linarith : ¬t < 0)]
  exact mul_le_mul_of_nonneg_left (hf.tsum_le_tsum hfle hp) hlam.le

#print axioms solution
