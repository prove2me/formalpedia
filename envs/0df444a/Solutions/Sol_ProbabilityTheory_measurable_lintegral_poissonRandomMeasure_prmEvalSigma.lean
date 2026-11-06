-- Prove2me | solution 1 for ProbabilityTheory.measurable_lintegral_poissonRandomMeasure_prmEvalSigma
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:37:29.730905+00:00
-- url     : https://prove2.me/submissions/50571e4b-5175-4c17-b723-30bab6b72609

import Definitions.Def_LeanLevy_RandomMeasure_PoissonFiltration
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory ProbabilityTheory Filter Set Topology Finset
open scoped ENNReal

theorem solution :
    ∀ {Ω E : Type} [MeasurableSpace E]
      {K : ℕ → Ω → ℕ} {X : ℕ → ℕ → Ω → E} {m : Measure E} {R : Set E},
      MeasurableSet R → m R < ⊤ → ∀ {g : E → ℝ≥0∞}, Measurable g →
        (∀ x, x ∉ R → g x = 0) →
        Measurable[prmEvalSigma K X m R]
          (fun ω => ∫⁻ x, g x ∂(poissonRandomMeasure K X ω)) := by
  intro Ω E _ K X m R _hR hRfin g hg hgR
  have hEval (B : Set E) (hB : MeasurableSet B) (hBR : B ⊆ R) (hfin : m B < ⊤) :
      Measurable[prmEvalSigma K X m R]
        (fun ω => poissonRandomMeasure K X ω B) :=
    Measurable.of_comap_le <| le_iSup (fun B' : prmEvalIndex m R =>
      MeasurableSpace.comap (fun ω => poissonRandomMeasure K X ω B'.1) inferInstance)
      ⟨B, hB, hBR, hfin⟩
  have hfiber : ∀ (n : ℕ) {y : ℝ≥0∞}, y ≠ 0 → SimpleFunc.eapprox g n ⁻¹' {y} ⊆ R := by
    intro n y hy x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    by_contra hxR
    have hle : SimpleFunc.eapprox g n x ≤ g x := by
      have h := le_iSup (fun k => SimpleFunc.eapprox g k x) n
      rwa [SimpleFunc.iSup_eapprox_apply hg x] at h
    rw [hx, hgR x hxR, le_zero_iff] at hle
    exact hy hle
  have hsimple : ∀ n : ℕ, Measurable[prmEvalSigma K X m R]
      fun ω => (SimpleFunc.eapprox g n).lintegral (poissonRandomMeasure K X ω) := by
    intro n
    simp only [SimpleFunc.lintegral]
    refine Finset.measurable_sum _ fun y _ => ?_
    by_cases hy : y = 0
    · simp only [hy, zero_mul]; exact measurable_const
    · exact (hEval ((SimpleFunc.eapprox g n) ⁻¹' {y})
        ((SimpleFunc.eapprox g n).measurableSet_fiber y)
        (hfiber n hy) (lt_of_le_of_lt (measure_mono (hfiber n hy)) hRfin)).const_mul y
  have hcongr : (fun ω => ∫⁻ x, g x ∂(poissonRandomMeasure K X ω))
      = fun ω => ⨆ n : ℕ, (SimpleFunc.eapprox g n).lintegral (poissonRandomMeasure K X ω) :=
    funext fun ω => lintegral_eq_iSup_eapprox_lintegral hg
  rw [hcongr]
  exact Measurable.iSup hsimple
