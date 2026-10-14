-- Prove2me | solution 1 for TPG.tendstoNormal_of_charFun
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-10-12T04:40:37.902403+00:00
-- url     : https://prove2.me/submissions/c82cafe8-b38b-4270-a63d-ec4e8d2877ef

import Mathlib
import Definitions.Def_TPG_Model
import Definitions.Def_TPG_Estimators
import Definitions.Def_TPG_Inference
import Theorems.Thm_TPG_isProbabilityMeasure_trajLaw

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
open TPG

theorem solution {S : Type} [Fintype S] [MeasurableSpace S] [MeasurableSingletonClass S]
    (E : Env S) (W : (T : ℕ) → Traj S T → ℝ) (hW : ∀ T : ℕ, Measurable (W T))
    (v : ℝ) (hv : 0 ≤ v)
    (h : ∀ t : ℝ, Filter.Tendsto
      (fun T : ℕ => ∫ ω, Complex.exp (Complex.I * (t : ℂ) * (W T ω : ℂ)) ∂(E.expLaw T (1 / 2)))
      Filter.atTop (nhds (Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2)))) :
    E.TendstoNormal W v := by
  have hprob : ∀ T : ℕ, IsProbabilityMeasure (E.expLaw T (1 / 2)) := fun T =>
    isProbabilityMeasure_trajLaw E T (fun _ => 1 / 2) (fun _ => ⟨by norm_num, by norm_num⟩)
  have hprobmap : ∀ T : ℕ, IsProbabilityMeasure ((E.expLaw T (1 / 2)).map (W T)) := fun T =>
    Measure.isProbabilityMeasure_map (hW T).aemeasurable
  -- the laws of the statistics and the limiting normal law, as probability measures on `ℝ`
  let ν : ℕ → ProbabilityMeasure ℝ := fun T => ⟨(E.expLaw T (1 / 2)).map (W T), hprobmap T⟩
  let ν₀ : ProbabilityMeasure ℝ := ⟨gaussianReal 0 (Real.toNNReal v), inferInstance⟩
  -- weak convergence from convergence of characteristic functions
  have hconv : Filter.Tendsto ν Filter.atTop (nhds ν₀) := by
    apply ProbabilityMeasure.tendsto_of_tendsto_charFun
    intro t
    have e1 : ∀ T : ℕ, charFun (ν T : Measure ℝ) t
        = ∫ ω, Complex.exp (Complex.I * (t : ℂ) * (W T ω : ℂ)) ∂(E.expLaw T (1 / 2)) := by
      intro T
      change charFun ((E.expLaw T (1 / 2)).map (W T)) t = _
      rw [charFun_apply_real, integral_map (hW T).aemeasurable (by fun_prop)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
      change Complex.exp ((t : ℂ) * (W T ω : ℂ) * Complex.I)
        = Complex.exp (Complex.I * (t : ℂ) * (W T ω : ℂ))
      congr 1
      ring
    have e2 : charFun (ν₀ : Measure ℝ) t = Complex.exp (-((v : ℂ) * (t : ℂ) ^ 2) / 2) := by
      change charFun (gaussianReal 0 (Real.toNNReal v)) t = _
      rw [charFun_gaussianReal]
      congr 1
      have hcoe : ((Real.toNNReal v : ℝ) : ℂ) = (v : ℂ) := by
        rw [Real.coe_toNNReal v hv]
      rw [hcoe, Complex.ofReal_zero]
      ring
    simp only [e1, e2]
    exact h t
  intro f
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hconv) f
  have e3 : ∀ T : ℕ, ∫ x, f x ∂(ν T : Measure ℝ) = ∫ ω, f (W T ω) ∂(E.expLaw T (1 / 2)) :=
    fun T => integral_map (hW T).aemeasurable f.continuous.aestronglyMeasurable
  simp only [e3] at hf
  exact hf
