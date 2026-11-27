-- Prove2me | solution 1 for SellVsPPU.Duopoly.a21_profits_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T22:16:43.940622+00:00
-- url     : https://prove2.me/submissions/136c7c8e-888b-4084-bc95-bc9cd726a9f6

import Mathlib
import Definitions.Def_SellVsPPU_Duopoly_Model
namespace SellVsPPU.Duopoly

theorem _root_.solution (P : Params) (hP : P.Admissible)
    (ps pu : ℝ) (hpu : 0 < pu) (hpuA : pu ≤ P.a)
    (hps0 : 0 ≤ ps) (hpsq : ps ≤ P.qm * pu) :
    profitS P ps pu = (ps - P.c) * (P.qm - ps / pu) / P.qm ∧
    profitU P ps pu = ps ^ 2 * (pu - cu P) / (2 * P.qm * pu ^ 2) := by
  obtain ⟨ha, hq, hc, hd, -⟩ := hP
  have hb0 : 0 ≤ ps / pu := div_nonneg hps0 hpu.le
  have hbq : ps / pu ≤ P.qm := by rw [div_le_iff₀ hpu]; exact hpsq
  have hS : sellSet P ps pu = Set.Icc (ps / pu) P.qm := by
    ext q
    simp only [sellSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc, div_le_iff₀ hpu]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      exact ⟨by nlinarith, h1⟩
    · rintro ⟨h0, h2⟩
      have hq0 : 0 ≤ q := le_trans hb0 ((div_le_iff₀ hpu).2 h0)
      refine ⟨⟨hq0, h2⟩, ?_, by nlinarith⟩
      nlinarith [mul_le_mul_of_nonneg_left hpuA hq0]
  have hU : ppuSet P ps pu = Set.Icc 0 (ps / pu) := by
    ext q
    simp only [ppuSet, Us, Uu, Set.mem_ofPred_eq, Set.mem_Icc, le_div_iff₀ hpu]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2, h3⟩
      exact ⟨h0, by nlinarith⟩
    · rintro ⟨h0, h2⟩
      refine ⟨⟨h0, le_trans ((le_div_iff₀ hpu).2 h2) hbq⟩, mul_nonneg h0 (sub_nonneg.2 hpuA), by nlinarith⟩
  constructor
  · unfold profitS
    rw [hS, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hbq)]
  · unfold profitU
    rw [hU, MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hb0, integral_id]
    field_simp
    ring


end SellVsPPU.Duopoly

