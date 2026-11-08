-- Prove2me | solution 1 for Underdogs.posterior_FS_eq
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:21:13.825603+00:00
-- url     : https://prove2.me/submissions/2d7cf8b5-06b7-44b9-b195-bcab3421c264

import Mathlib
import Definitions.Def_Underdogs_Params_Standing
import Definitions.Def_Underdogs_Params_posteriorHigh

namespace Aux_Q01_posterior_FS_eq
open Underdogs MeasureTheory ProbabilityTheory

theorem sumQ (f : Quality → ENNReal) : ∑ q, f q = f Quality.H + f Quality.L := by
  show ∑ q ∈ ({Quality.H, Quality.L} : Finset Quality), f q = _
  rw [Finset.sum_pair (by decide)]

theorem law_apply (P : Params) (T : Set (Quality × Bool × Bool)) :
    P.jointLaw T = ∑ ω, ENNReal.ofReal (P.mass ω) * T.indicator 1 ω := by
  unfold Params.jointLaw
  rw [Measure.finsetSum_apply]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  rw [Measure.smul_apply, Measure.dirac_apply, smul_eq_mul]

theorem sum8 (f : Quality × Bool × Bool → ENNReal) :
    ∑ ω, f ω = f (Quality.H, false, false) + f (Quality.H, false, true) +
      f (Quality.H, true, false) + f (Quality.H, true, true) +
      (f (Quality.L, false, false) + f (Quality.L, false, true) +
        f (Quality.L, true, false) + f (Quality.L, true, true)) := by
  rw [Fintype.sum_prod_type, sumQ]
  simp only [Fintype.sum_prod_type, Fintype.sum_bool]
  ring

end Aux_Q01_posterior_FS_eq

open Underdogs MeasureTheory ProbabilityTheory in
theorem solution (P : Params) (hP : P.Standing) :
    P.posteriorHigh false true =
        P.phF * (1 - P.ph) * 0.5 / (P.phF * (1 - P.ph) * 0.5 + P.plF * (1 - P.pl) * 0.5) ∧
      P.posteriorHigh false true = 1 / (1 + P.plF * (1 - P.pl) / (P.phF * (1 - P.ph))) := by
  obtain ⟨⟨hph0, hph1⟩, ⟨hpl0, hpl1⟩, -, -, ⟨hphF0, -⟩, ⟨hplF0, -⟩⟩ := hP
  have hS : MeasurableSet {ω : Quality × Bool × Bool | ω.2 = (false, true)} :=
    (Set.toFinite _).measurableSet
  have hden : P.jointLaw {ω : Quality × Bool × Bool | ω.2 = (false, true)} =
      ENNReal.ofReal (P.mass (Quality.H, false, true)) +
        ENNReal.ofReal (P.mass (Quality.L, false, true)) := by
    rw [Aux_Q01_posterior_FS_eq.law_apply, Aux_Q01_posterior_FS_eq.sum8]
    simp [Set.indicator]
  have hnum : P.jointLaw ({ω : Quality × Bool × Bool | ω.2 = (false, true)} ∩
      {ω : Quality × Bool × Bool | ω.1 = Quality.H}) =
      ENNReal.ofReal (P.mass (Quality.H, false, true)) := by
    rw [Aux_Q01_posterior_FS_eq.law_apply, Aux_Q01_posterior_FS_eq.sum8]
    simp [Set.indicator]
  have hx : P.mass (Quality.H, false, true) = 1 / 2 * (1 - P.ph) * P.phF := by
    simp [Params.mass]
  have hy : P.mass (Quality.L, false, true) = 1 / 2 * (1 - P.pl) * P.plF := by
    simp [Params.mass]
  have hx0 : 0 < 1 / 2 * (1 - P.ph) * P.phF := by
    have : 0 < 1 - P.ph := by linarith
    positivity
  have hy0 : 0 < 1 / 2 * (1 - P.pl) * P.plF := by
    have : 0 < 1 - P.pl := by linarith
    positivity
  have hpost : P.posteriorHigh false true =
      (1 / 2 * (1 - P.ph) * P.phF) / (1 / 2 * (1 - P.ph) * P.phF + 1 / 2 * (1 - P.pl) * P.plF) := by
    unfold Params.posteriorHigh
    rw [cond_apply hS, hden, hnum, hx, hy, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hx0.le, ENNReal.toReal_ofReal hy0.le]
    exact (div_eq_inv_mul _ _).symm
  have hX : 0 < P.phF * (1 - P.ph) := by
    have : 0 < 1 - P.ph := by linarith
    positivity
  have h05 : (0.5 : ℝ) = 1 / 2 := by norm_num
  constructor
  · rw [hpost, h05]
    ring
  · rw [hpost, one_add_div hX.ne', one_div_div,
      show (1 / 2 : ℝ) * (1 - P.ph) * P.phF = 1 / 2 * (P.phF * (1 - P.ph)) by ring,
      show (1 / 2 : ℝ) * (1 - P.pl) * P.plF = 1 / 2 * (P.plF * (1 - P.pl)) by ring,
      ← mul_add, mul_div_mul_left _ _ (by norm_num : (1 / 2 : ℝ) ≠ 0)]
