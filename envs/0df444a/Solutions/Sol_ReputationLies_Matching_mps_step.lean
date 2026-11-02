-- Prove2me | solution 1 for ReputationLies.Matching.mps_step
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T10:55:28.111208+00:00
-- url     : https://prove2.me/submissions/0f41df10-153a-44f9-9b58-4d155070d171

import Mathlib
import Definitions.Def_ReputationLies_Matching_Model

open Set ReputationLies.Matching

theorem solution (P : Primitives) (hP : P.Standing) :
    (StrictConvexOn ℝ (Icc 0 1) P.F → StrictMonoOn P.gambleHire (Ioc P.sL 1)) ∧
    (StrictConcaveOn ℝ (Icc 0 1) P.F → StrictAntiOn P.gambleHire (Ioc P.sL 1)) := by
  obtain ⟨hsL, hsLH, hsH1, hp0, hp1, -⟩ := hP
  have hk : 0 < P.shat - P.sL := by unfold Primitives.shat; nlinarith
  have hform : ∀ s ∈ Ioc P.sL 1, P.gambleHire s =
      P.F P.sL + (P.shat - P.sL) * ((P.F s - P.F P.sL) / (s - P.sL)) := by
    intro s hs
    have : s - P.sL ≠ 0 := by linarith [hs.1]
    unfold Primitives.gambleHire
    field_simp
    ring
  have hsLI : P.sL ∈ Icc (0:ℝ) 1 := ⟨hsL.le, by linarith⟩
  constructor
  · intro hF s hs t ht hst
    rw [hform s hs, hform t ht]
    have := hF.secant_strict_mono_aux2 hsLI ⟨by linarith [ht.1], ht.2⟩ hs.1 hst
    have := mul_lt_mul_of_pos_left this hk
    linarith
  · intro hF s hs t ht hst
    rw [hform s hs, hform t ht]
    have := hF.neg.secant_strict_mono_aux2 hsLI ⟨by linarith [ht.1], ht.2⟩ hs.1 hst
    simp only [Pi.neg_apply] at this
    have h2 : (P.F t - P.F P.sL) / (t - P.sL) < (P.F s - P.F P.sL) / (s - P.sL) := by
      have e1 : (-P.F s - -P.F P.sL) / (s - P.sL) = -((P.F s - P.F P.sL) / (s - P.sL)) := by ring
      have e2 : (-P.F t - -P.F P.sL) / (t - P.sL) = -((P.F t - P.F P.sL) / (t - P.sL)) := by ring
      rw [e1, e2] at this; linarith
    have := mul_lt_mul_of_pos_left h2 hk
    linarith
