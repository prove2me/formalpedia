-- Prove2me | solution 1 for StochLoadBal.Makespan.effSize_facts
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-20T17:56:11.90009+00:00
-- url     : https://prove2.me/submissions/0a376ae1-dc16-4295-8548-f81a7d2b4d81

import Mathlib
import Definitions.Def_StochLoadBal_Makespan_Model

-- Source mathematics: Anupam Gupta, Amit Kumar, Viswanath Nagarajan and Xiangkun Shen.
-- Formal model and integrability qualifications: mikedeng1; statement review: Shuze Chen.
-- Research directed by Alexander Richard Towell (queelius).
-- Formalization developed and checked with substantial OpenAI Codex assistance.
open MeasureTheory ProbabilityTheory StochLoadBal.Makespan

namespace EffectiveSizeResearch
lemma bounded_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hm : Measurable Y)
    (hb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) : Integrable Y P := by
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  simpa [Real.norm_eq_abs, abs_of_nonneg (hb ω).1] using (hb ω).2

lemma integral_bounds {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → ℝ) (hm : Measurable Y)
    (hb : ∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) :
    0 ≤ ∫ ω, Y ω ∂P ∧ ∫ ω, Y ω ∂P ≤ 1 := by
  refine ⟨integral_nonneg (fun ω => (hb ω).1), ?_⟩
  have hh := integral_mono (bounded_integrable P Y hm hb) (integrable_const (1 : ℝ))
    (fun ω => (hb ω).2)
  simpa using hh
end EffectiveSizeResearch

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (k : ℕ) (hk : 1 ≤ k) :
    (∀ Y : Ω → ℝ, Measurable Y → (∀ ω, 0 ≤ Y ω ∧ Y ω ≤ 1) →
      0 ≤ effSize P k Y ∧ effSize P k Y ≤ 1) ∧
    (∀ Y : Ω → ℝ, Measurable Y → Integrable Y P →
      Integrable (fun ω => Real.exp (Real.log k * Y ω)) P →
      ∫ ω, Y ω ∂P ≤ effSize P k Y) := by
  by_cases hk1 : k = 1
  · subst k
    simp only [effSize, ↓reduceIte]
    exact ⟨fun Y hm hb => EffectiveSizeResearch.integral_bounds P Y hm hb,
      fun _ _ _ _ => le_rfl⟩
  have hkR : 1 < (k : ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hl : 0 < Real.log (k : ℝ) := Real.log_pos hkR
  constructor
  · intro Y hm hb
    have hlo (ω) : 1 ≤ Real.exp (Real.log k * Y ω) :=
      Real.one_le_exp_iff.mpr (mul_nonneg hl.le (hb ω).1)
    have hup (ω) : Real.exp (Real.log k * Y ω) ≤ (k : ℝ) := by
      calc
        _ ≤ Real.exp (Real.log (k : ℝ)) :=
          Real.exp_le_exp.mpr (mul_le_of_le_one_right hl.le (hb ω).2)
        _ = _ := Real.exp_log (zero_lt_one.trans hkR)
    have hint : Integrable (fun ω => Real.exp (Real.log k * Y ω)) P := by
      apply (integrable_const (k : ℝ)).mono'
        (Real.continuous_exp.measurable.comp (measurable_const.mul hm)).aestronglyMeasurable
      filter_upwards [] with ω
      simpa [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hup ω
    have hlow : 1 ≤ ∫ ω, Real.exp (Real.log k * Y ω) ∂P := by
      simpa using integral_mono (integrable_const (1 : ℝ)) hint hlo
    have hupper : (∫ ω, Real.exp (Real.log k * Y ω) ∂P) ≤ (k : ℝ) := by
      simpa using integral_mono hint (integrable_const (k : ℝ)) hup
    rw [effSize, if_neg hk1]
    refine ⟨div_nonneg (Real.log_nonneg hlow) hl.le, ?_⟩
    apply (div_le_one hl).mpr
    exact Real.log_le_log (zero_lt_one.trans_le hlow) hupper
  · intro Y _ hY hExp
    have hj := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn
      isClosed_univ (Filter.Eventually.of_forall (fun _ => Set.mem_univ _))
      (hY.const_mul (Real.log k)) hExp
    rw [integral_const_mul] at hj
    have hlog := Real.log_le_log (Real.exp_pos _) hj
    rw [Real.log_exp] at hlog
    rw [effSize, if_neg hk1]
    apply (le_div_iff₀ hl).mpr
    simpa [mul_comm] using hlog

#print axioms solution
