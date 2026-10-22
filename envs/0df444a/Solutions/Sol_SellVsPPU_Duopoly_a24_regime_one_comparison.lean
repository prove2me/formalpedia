-- Prove2me | solution 1 for SellVsPPU.Duopoly.a24_regime_one_comparison
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:49:26.717701+00:00
-- url     : https://prove2.me/submissions/f0a2debc-ab30-4562-b940-b7ce61adc678

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model
set_option autoImplicit false

open SellVsPPU.Duopoly

theorem solution (P : Params) (hP : P.Admissible)
    (hregime : P.c ≤ P.qm * (P.a / 2 - P.delta)) :
    (profSStar P = profUStar P ↔
      (5 * P.c + 6 * P.delta * P.qm) * (P.c - 2 * P.delta * P.qm) = 0) ∧
    (profSStar P ≤ profUStar P ↔ P.delta ≤ P.c / (2 * P.qm)) ∧
    (P.c = 2 * P.delta * P.qm → P.delta ≤ P.a / 6) := by
  obtain ⟨ha, hq, hc, hd, -⟩ := hP
  have hD : 0 < P.c + P.delta * P.qm := by positivity
  have hdiff : profUStar P - profSStar P
      = (5 * P.c + 6 * P.delta * P.qm) * (P.c - 2 * P.delta * P.qm) / (32 * (P.c + P.delta * P.qm)) := by
    unfold profUStar profSStar
    rw [if_pos hregime, if_pos hregime]
    field_simp
    ring
  have h5 : 0 < 5 * P.c + 6 * P.delta * P.qm := by positivity
  have h32 : 0 < 32 * (P.c + P.delta * P.qm) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have : profUStar P - profSStar P = 0 := by linarith
      rw [hdiff, div_eq_zero_iff] at this
      rcases this with h' | h'
      · exact h'
      · exact absurd h' h32.ne'
    · intro h
      have : profUStar P - profSStar P = 0 := by rw [hdiff, h]; simp
      linarith
  · rw [le_div_iff₀ (by positivity)]
    constructor
    · intro h
      have h0 : 0 ≤ profUStar P - profSStar P := by linarith
      rw [hdiff] at h0
      have h1 : 0 ≤ (5 * P.c + 6 * P.delta * P.qm) * (P.c - 2 * P.delta * P.qm) :=
        (div_nonneg_iff.1 h0).elim (fun h => h.1) (fun h => by linarith [h.2, h32])
      have := nonneg_of_mul_nonneg_right h1 h5
      · nlinarith
    · intro h
      have h1 : 0 ≤ (5 * P.c + 6 * P.delta * P.qm) * (P.c - 2 * P.delta * P.qm) :=
        mul_nonneg h5.le (by nlinarith)
      have h0 : 0 ≤ profUStar P - profSStar P := by rw [hdiff]; positivity
      linarith
  · intro h
    have : 2 * P.delta * P.qm ≤ P.qm * (P.a / 2 - P.delta) := by linarith
    have h2 : 3 * P.delta ≤ P.a / 2 := by
      by_contra hn
      push_neg at hn
      nlinarith
    linarith
