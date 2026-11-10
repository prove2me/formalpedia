-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intake100.P23.weylRelations_consequences
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-10T04:05:53.491902+00:00
-- url     : https://prove2.me/submissions/131eac80-7796-4ad7-b556-ecd746fead40

import Definitions.Def_QAlgorithms_Papers_Independent_Intake100_P23

noncomputable section

open scoped BigOperators

open QAlgorithms.Papers.Independent.Intake100.P23 in
theorem solution {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (omega : Y →ₗ[ℝ] Y →ₗ[ℝ] ℝ)
    (hanti : Antisymmetric omega) (W : Y → H →L[ℂ] H) (hW : IsCCR omega W) :
    (∀ y z, W y * W z = Complex.exp (-Complex.I * (omega y z : ℂ)) • (W z * W y)) ∧
    (∀ y, star (W y) = W (-y)) ∧ W 0 = 1 ∧
    (∀ (y : Y) (s t : ℝ), W (s • y) * W (t • y) = W ((s + t) • y)) := by
  have hyy : ∀ y, omega y y = 0 := by
    intro y
    have := hanti y y
    linarith
  have hzero : ∀ y z, omega y z = 0 → W y * W z = W (y + z) := by
    intro y z h
    rw [hW.2 y z, h]
    simp
  have hW0 : W 0 = 1 := by
    have h0 : W 0 * W 0 = W 0 := by
      rw [hzero 0 0 (hyy 0), add_zero]
    have hu := Unitary.star_mul_self_of_mem (hW.1 0)
    calc W 0 = star (W 0) * W 0 * W 0 := by rw [hu, one_mul]
      _ = star (W 0) * (W 0 * W 0) := by rw [mul_assoc]
      _ = 1 := by rw [h0, hu]
  refine ⟨fun y z => ?_, fun y => ?_, hW0, fun y s t => ?_⟩
  · have h2 := hW.2 z y
    rw [add_comm z y, hanti z y] at h2
    rw [hW.2 y z, h2, smul_smul, ← Complex.exp_add]
    congr 1
    congr 1
    push_cast
    ring
  · have hinv : W y * W (-y) = 1 := by
      have : omega y (-y) = 0 := by rw [map_neg, hyy, neg_zero]
      rw [hzero y (-y) this, add_neg_cancel, hW0]
    have hu := Unitary.star_mul_self_of_mem (hW.1 y)
    calc star (W y) = star (W y) * (W y * W (-y)) := by rw [hinv, mul_one]
      _ = W (-y) := by rw [← mul_assoc, hu, one_mul]
  · have h : omega (s • y) (t • y) = 0 := by
      rw [LinearMap.map_smul₂, map_smul, hyy, smul_zero, smul_zero]
    rw [hzero _ _ h, add_smul]
