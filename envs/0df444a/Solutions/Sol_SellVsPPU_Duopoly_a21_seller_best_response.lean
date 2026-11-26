-- Prove2me | solution 1 for SellVsPPU.Duopoly.a21_seller_best_response
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:52:08.295855+00:00
-- url     : https://prove2.me/submissions/e9fd1d6c-39cd-4b1a-8974-eb231e888609

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model
namespace SellVsPPU.Duopoly

/-- Stronger than printed: the paper derives this price from a first-order condition; this theorem asserts global optimality over every real seller price. -/
theorem _root_.solution (P : Params) (hP : P.Admissible)
    (pu : ℝ) (hpu : 0 < pu) (hpuA : pu ≤ P.a) (hc : P.c ≤ P.qm * pu) :
    ∀ ps' : ℝ, profitS P ps' pu ≤ profitS P ((P.c + P.qm * pu) / 2) pu := by
  obtain ⟨ha, hq, hc0, hd, -⟩ := hP
  have hset : ∀ ps : ℝ, sellSet P ps pu = Set.Icc (max 0 (ps / pu)) P.qm := by
    intro ps
    ext q
    simp only [sellSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc, max_le_iff, div_le_iff₀ hpu]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      exact ⟨⟨h0, by nlinarith⟩, h1⟩
    · rintro ⟨⟨h0, h1⟩, h2⟩
      refine ⟨⟨h0, h2⟩, ?_, by nlinarith⟩
      nlinarith [mul_le_mul_of_nonneg_left hpuA h0]
  have hv : ∀ ps : ℝ, profitS P ps pu = (ps - P.c) * max (P.qm - max 0 (ps / pu)) 0 / P.qm := by
    intro ps
    unfold profitS
    rw [hset, Real.volume_Icc, ENNReal.toReal_ofReal']
  intro ps'
  rw [hv, hv]
  apply div_le_div_of_nonneg_right _ hq.le
  set s := (P.c + P.qm * pu) / 2 with hs
  have hs0 : 0 ≤ s / pu := div_nonneg (by rw [hs]; positivity) hpu.le
  have hsq : s / pu ≤ P.qm := by rw [div_le_iff₀ hpu, hs]; linarith
  have hsc : 0 ≤ s - P.c := by rw [hs]; linarith
  rw [max_eq_right hs0, max_eq_left (sub_nonneg.2 hsq)]
  have hR : 0 ≤ (s - P.c) * (P.qm - s / pu) := mul_nonneg hsc (sub_nonneg.2 hsq)
  by_cases h1 : ps' ≤ P.c
  · exact le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (le_max_right _ _)) hR
  have h2 : 0 ≤ ps' / pu := div_nonneg (by linarith) hpu.le
  rw [max_eq_right h2]
  by_cases h3 : ps' / pu ≤ P.qm
  · rw [max_eq_left (sub_nonneg.2 h3)]
    have e : ∀ y : ℝ, (y - P.c) * (P.qm - y / pu) = (y - P.c) * (P.qm * pu - y) / pu := by
      intro y; field_simp
    rw [e, e]
    apply div_le_div_of_nonneg_right _ hpu.le
    rw [hs]
    nlinarith [sq_nonneg (ps' - (P.c + P.qm * pu) / 2)]
  · rw [max_eq_right (by linarith), mul_zero]; exact hR


end SellVsPPU.Duopoly

