-- Prove2me | solution 1 for ShortWDRODual.MaxCost.coupling_form
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T10:09:11.67674+00:00
-- url     : https://prove2.me/submissions/c9877203-0f42-4e7f-8495-2c8994f80ff7

import Mathlib
import Definitions.Def_ModelRiskOT_Duality_extIntegral
import Definitions.Def_ShortWDRODual_MaxCost_Setting
import Theorems.Thm_ShortWDRODual_MaxCost_IP_psi

open MeasureTheory ModelRiskOT.Duality ShortWDRODual.MaxCost
open scoped ENNReal

theorem solution {X : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X]
    [BorelSpace X] (Phat : Measure X) [IsProbabilityMeasure Phat]
    (f : X → ℝ) (hf : Measurable f) (hfint : ⊥ < extIntegral Phat (fun x => (f x : EReal)))
    (c : X → X → ℝ) (hc : Continuous (fun q : X × X => c q.1 q.2))
    (hcnn : ∀ x y, 0 ≤ c x y) (hc0 : ∀ x, c x x = 0)
    (ρ : ℝ) (hρ : 0 ≤ ρ) :
    (⨆ γ ∈ {γ : Measure (X × X) | γ ∈ ShortWDRODual.Legendre.couplingsFst Phat ∧
        essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ},
        extIntegral γ (fun q => (f q.2 : EReal))) =
      extIntegral Phat (localSup c f ρ) := by
  obtain ⟨-, -, -, hIPeq⟩ := IP_psi Phat f hf c hc hcnn hc0 ρ hρ
  have hsup : ShortWDRODual.Legendre.supFn (psi c f ρ) = localSup c f ρ := by
    funext xh
    unfold ShortWDRODual.Legendre.supFn psi localSup
    apply iSup_congr
    intro x
    by_cases h : c xh x ≤ ρ
    · simp [h, not_lt.mpr h]
    · simp [h, lt_of_not_ge h]
  rw [← hsup, hIPeq]
  -- on couplings concentrated on `{c ≤ ρ}`, `ψ_ρ = f(X)` almost everywhere
  have heq : ∀ γ : Measure (X × X),
      essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ →
      extIntegral γ (fun q => (f q.2 : EReal)) = extIntegral γ (psi c f ρ) := by
    intro γ hγ
    have hae : ∀ᵐ q ∂γ, psi c f ρ q = (f q.2 : EReal) := by
      filter_upwards [ENNReal.ae_le_essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2))]
        with q hq0
      have hq := hq0.trans hγ
      have : c q.1 q.2 ≤ ρ := (ENNReal.ofReal_le_ofReal_iff hρ).mp hq
      simp [psi, not_lt.mpr this]
    have h1 : (fun q : X × X => ((f q.2 : EReal)).toENNReal) =ᵐ[γ]
        fun q => (psi c f ρ q).toENNReal := hae.mono fun q hq => by simp only [hq]
    have h2 : (fun q : X × X => (-(f q.2 : EReal)).toENNReal) =ᵐ[γ]
        fun q => (-psi c f ρ q).toENNReal := hae.mono fun q hq => by simp only [hq]
    unfold extIntegral
    rw [lintegral_congr_ae h1, lintegral_congr_ae h2]
  apply le_antisymm
  · refine iSup₂_le fun γ hγ => ?_
    rw [heq γ hγ.2]
    exact le_iSup₂ (f := fun γ (_ : γ ∈ ShortWDRODual.Legendre.couplingsFst Phat) =>
      extIntegral γ (psi c f ρ)) γ hγ.1
  · refine iSup₂_le fun γ hγ => ?_
    by_cases hess : essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ
    · rw [← heq γ hess]
      exact le_iSup₂ (f := fun γ (_ : γ ∈ {γ : Measure (X × X) | γ ∈
        ShortWDRODual.Legendre.couplingsFst Phat ∧
        essSup (fun q : X × X => ENNReal.ofReal (c q.1 q.2)) γ ≤ ENNReal.ofReal ρ}) =>
        extIntegral γ (fun q => (f q.2 : EReal))) γ ⟨hγ, hess⟩
    · -- otherwise `ψ_ρ = −∞` on a set of positive measure, so the integral is `−∞`
      let B : Set (X × X) := {q | ρ < c q.1 q.2}
      have hB : MeasurableSet B := (isOpen_lt continuous_const hc).measurableSet
      have hBpos : γ B ≠ 0 := by
        intro h0
        apply hess
        refine essSup_le_of_ae_le _ ?_
        have : ∀ᵐ q ∂γ, q ∉ B := measure_eq_zero_iff_ae_notMem.mp h0
        filter_upwards [this] with q hq
        exact ENNReal.ofReal_le_ofReal (not_lt.mp hq)
      have htop : ∫⁻ q, (-(psi c f ρ q)).toENNReal ∂γ = ⊤ := by
        apply eq_top_iff.mpr
        calc (⊤ : ℝ≥0∞) = ∫⁻ q, B.indicator (fun _ => (⊤ : ℝ≥0∞)) q ∂γ := by
              rw [lintegral_indicator_const hB, ENNReal.top_mul hBpos]
          _ ≤ ∫⁻ q, (-(psi c f ρ q)).toENNReal ∂γ := by
              apply lintegral_mono
              intro q
              by_cases hq : q ∈ B
              · have : ρ < c q.1 q.2 := hq
                simp [Set.indicator_of_mem hq, psi, this]
              · simp [Set.indicator_of_notMem hq]
      have hbot : extIntegral γ (psi c f ρ) = ⊥ := by
        unfold extIntegral
        rw [htop]
        exact EReal.sub_top _
      rw [hbot]
      exact bot_le
