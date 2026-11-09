-- Prove2me | solution 1 for QGChasing.eq_4_first_case
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T06:37:49.316654+00:00
-- url     : https://prove2.me/submissions/83c02880-1e0f-4089-98c8-d23fd3313408

import Mathlib
import Definitions.Def_QGChasing_InFkappa
import Definitions.Def_SuperPolyak_solutionSet
import Definitions.Def_QGChasing_cpdBeta
import Definitions.Def_QGChasing_cpdC

open QGChasing in
theorem solution {d : ℕ} (κ : ℝ) (hκ : 1 ≤ κ) (X : Set (EuclideanSpace ℝ (Fin d))) (hXc : IsClosed X) (hXcv : Convex ℝ X)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : InFkappa κ f) (p : EuclideanSpace ℝ (Fin d)) (hp : p ∈ X)
    (v : EuclideanSpace ℝ (Fin d)) (hv : ∀ z, f v ≤ f z) (vX : EuclideanSpace ℝ (Fin d))
    (hvX : vX ∈ SuperPolyak.nearestPoints {z | z ∈ X ∧ ∀ w ∈ X, f z - f v ≤ f w - f v} p)
    (htest : cpdBeta κ * ‖vX - p‖ ≤ f vX - f v) (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ X) :
    (f vX - f v) + ‖vX - p‖ + cpdC κ * (‖vX - u‖ - ‖p - u‖) ≤ cpdC κ * (f u - f v) := by
  have h1 : f vX - f v ≤ f u - f v := hvX.1.2 u hu
  have hk : 1 ≤ κ ^ (1 / 3 : ℝ) := Real.one_le_rpow hκ (by norm_num)
  obtain ⟨k, hkdef⟩ : ∃ k, k = κ ^ (1 / 3 : ℝ) := ⟨_, rfl⟩
  rw [← hkdef] at hk
  have hβ : cpdBeta κ = 1 + 3 * (1 / (2 * k)) := by
    unfold cpdBeta cpdR; rw [hkdef]
  have hC : cpdC κ = 32 / 7 * (1 + k) := by
    unfold cpdC; rw [hkdef]
  obtain ⟨r, hr⟩ : ∃ r, r = 1 / (2 * k) := ⟨_, rfl⟩
  have hk0 : 0 < k := by linarith
  have hrpos : 0 < r := by rw [hr]; positivity
  have hkr : k * r = 1 / 2 := by rw [hr]; field_simp
  rw [hβ, ← hr] at htest
  rw [hC]
  obtain ⟨C, hCdef⟩ : ∃ C, C = 32 / 7 * (1 + k) := ⟨_, rfl⟩
  rw [← hCdef]
  have hC1 : 0 ≤ C - 1 := by rw [hCdef]; linarith
  have hβC : 1 + C ≤ (C - 1) * (1 + 3 * r) := by
    rw [hCdef]; nlinarith [hkr, hrpos]
  have hδ : 0 ≤ ‖vX - p‖ := norm_nonneg _
  have hm1 := mul_le_mul_of_nonneg_right hβC hδ
  have hm2 := mul_le_mul_of_nonneg_left htest hC1
  have htri : ‖vX - u‖ ≤ ‖vX - p‖ + ‖p - u‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
  have hm3 : C * (‖vX - u‖ - ‖p - u‖) ≤ C * ‖vX - p‖ :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have hm4 : C * (f vX - f v) ≤ C * (f u - f v) := mul_le_mul_of_nonneg_left h1 (by linarith)
  nlinarith
