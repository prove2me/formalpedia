-- Prove2me | solution 1 for SelfGuidedALP.lemma_EC_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:51:34.848118+00:00
-- url     : https://prove2.me/submissions/31f5b00d-4e8f-4d05-8bc9-ca36ca145ba5

import Mathlib
import Definitions.Def_SelfGuidedALP_ELPFeasible
import Definitions.Def_SelfGuidedALP_IsOptimalValue

open MeasureTheory

open SelfGuidedALP in
theorem solution {d m : ℕ} (M : MDP d m) (Vstar V : EuclideanSpace ℝ (Fin d) → ℝ)
    (hVstar : IsOptimalValue M Vstar) (hcont : ContinuousOn V M.S) (hfeas : ELPFeasible M V) :
    ∀ s ∈ M.S, V s ≤ Vstar s := by
  obtain ⟨s0, hs0, hmax⟩ := M.isCompact_S.exists_isMaxOn M.nonempty_S (hcont.sub hVstar.1)
  have hmax' := isMaxOn_iff.mp hmax
  suffices h : V s0 - Vstar s0 ≤ 0 by
    intro s hs
    have := hmax' s hs
    simp only [Pi.sub_apply] at this
    linarith
  obtain ⟨a0, ha0, heq⟩ := (hVstar.2 s0 hs0).1
  simp only at heq
  haveI := M.isProbabilityMeasure_P s0 hs0 a0 ha0
  set P := M.P s0 a0 with hP
  have hSm : MeasurableSet M.S := M.isCompact_S.isClosed.measurableSet
  have hPc : P M.Sᶜ = 0 := by
    rw [measure_compl hSm (measure_ne_top _ _), M.P_S s0 hs0 a0 ha0, measure_univ]
    simp
  have hae : ∀ᵐ x ∂P, x ∈ M.S := by
    rw [ae_iff]
    simpa [Set.compl_def] using hPc
  have hrestr : P.restrict M.S = P := Measure.restrict_eq_self_of_ae_mem hae
  have hintV : Integrable V P := by
    have := hcont.integrableOn_compact (μ := P) M.isCompact_S
    rwa [IntegrableOn, hrestr] at this
  have hintV' : Integrable Vstar P := by
    have := hVstar.1.integrableOn_compact (μ := P) M.isCompact_S
    rwa [IntegrableOn, hrestr] at this
  have hf := hfeas s0 hs0 a0 ha0
  have hI : ∫ s', (V s' - Vstar s') ∂P ≤ V s0 - Vstar s0 := by
    have := integral_mono_ae (hintV.sub hintV') (integrable_const (V s0 - Vstar s0))
      (by
        filter_upwards [hae] with x hx
        exact hmax' x hx)
    simpa using this
  rw [integral_sub hintV hintV'] at hI
  have hγ0 := M.γ_nonneg
  have hγ1 := M.γ_lt_one
  have h2 := mul_le_mul_of_nonneg_left hI hγ0
  by_contra hpos
  push_neg at hpos
  nlinarith
