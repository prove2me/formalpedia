-- Prove2me | solution 1 for TeleDriving.AsymLimited.appD1_rho_gt
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T08:28:28.59574+00:00
-- url     : https://prove2.me/submissions/5ed4e529-62be-40be-9017-6a6ee9369a11

import Mathlib
import Definitions.Def_TeleDriving_ScarceFleet_Model

set_option autoImplicit false

theorem solution (s alpha : ℝ) (hs : 0 < s) (ha0 : 0 < alpha) (ha1 : alpha < 1) :
    ∀ lam : ℝ, 0 < lam → ∀ k : ℕ, k ∈ Finset.Icc 1 (TeleDriving.ScarceFleet.mLam alpha s lam) →
      1 / alpha < TeleDriving.ScarceFleet.rho (TeleDriving.ScarceFleet.muBesbes s) lam (TeleDriving.ScarceFleet.mLam alpha s lam) (k : ℝ) := by
  intro lam hlam k hk
  obtain ⟨hk1, hkm⟩ := Finset.mem_Icc.mp hk
  have hnn : 0 ≤ alpha * lam * s := by positivity
  have hkM : (k : ℝ) ≤ (TeleDriving.ScarceFleet.mLam alpha s lam : ℝ) := by exact_mod_cast hkm
  have hkA : (k : ℝ) ≤ alpha * lam * s := by
    have := (Nat.le_floor_iff hnn).mp hkm
    exact this
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
  set M := TeleDriving.ScarceFleet.mLam alpha s lam with hMdef
  have hpos : (0 : ℝ) < (M : ℝ) - k + 1 := by linarith
  have ha : 0 < Real.sqrt ((M : ℝ) - k + 1) := Real.sqrt_pos.mpr hpos
  set a := Real.sqrt ((M : ℝ) - k + 1) with hadef
  have hD : s < s / a + s := by have : 0 < s / a := by positivity
                                linarith
  have hDpos : 0 < s / a + s := by linarith
  unfold TeleDriving.ScarceFleet.rho TeleDriving.ScarceFleet.muBesbes
  have e : lam / ((k : ℝ) * (1 / (s / a + s))) = lam * (s / a + s) / k := by
    field_simp
  rw [e, lt_div_iff₀ hkpos]
  have h1 : 1 / alpha * k ≤ lam * s := by
    rw [one_div, inv_mul_le_iff₀ ha0]; nlinarith
  nlinarith
