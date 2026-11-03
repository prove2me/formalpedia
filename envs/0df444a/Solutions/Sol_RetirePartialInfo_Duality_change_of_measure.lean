-- Prove2me | solution 1 for RetirePartialInfo.Duality.change_of_measure
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T05:43:48.158973+00:00
-- url     : https://prove2.me/submissions/dd317bd1-6cac-4e6d-9215-1a4fdda0b0a9

import Mathlib
import Definitions.Def_RetirePartialInfo_Duality_Market

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open RetirePartialInfo.Duality

theorem solution {Ω : Type*} [MeasurableSpace Ω] (p : Params) (st : Setting Ω)
    (Iθ : ℝ≥0 → Ω → ℝ) (hst : st.Standing p) (hIto : IsItoIntegral p st (θ p st) Iθ)
    (h21 : Assumption21 p st Iθ) (t : ℝ≥0) (ht : (t : ℝ) ≤ p.T) (M : Ω → ℝ)
    (hM : StronglyMeasurable[FS p st t] M)
    (hint : Integrable (fun ω => Z p st Iθ p.Tn ω * M ω) st.P) :
    ∫ ω, M ω ∂(Pt p st Iθ) = ∫ ω, calZ p st Iθ t ω * M ω ∂st.P := by
  have : IsProbabilityMeasure st.P := hst.1
  have hZint : Integrable (Z p st Iθ p.Tn) st.P := by
    have := h21.2.integrable p.Tn
    simpa only [min_self] using this
  have hZpos : ∀ ω, 0 < Z p st Iθ p.Tn ω := fun ω => Real.exp_pos _
  have h1 : ∫ ω, M ω ∂(Pt p st Iθ) = ∫ ω, Z p st Iθ p.Tn ω * M ω ∂st.P := by
    unfold Pt
    have hae : AEMeasurable (fun ω => (Z p st Iθ p.Tn ω).toNNReal) st.P :=
      measurable_real_toNNReal.comp_aemeasurable hZint.aemeasurable
    have := integral_withDensity_eq_integral_smul₀ hae M
    simp only [ENNReal.ofReal] at *
    rw [this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    simp [NNReal.smul_def, Real.coe_toNNReal _ (hZpos ω).le]
  rw [h1]
  have hm := (FS p st).le t
  have h2 := integral_condExp hm (μ := st.P) (f := fun ω => Z p st Iθ p.Tn ω * M ω)
  rw [← h2]
  refine integral_congr_ae ?_
  have := condExp_mul_of_stronglyMeasurable_right (m := FS p st t) (μ := st.P)
    (f := Z p st Iθ p.Tn) hM hint hZint
  exact this.trans (Filter.Eventually.of_forall fun ω => rfl)
