-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.holomorphic_periodicity_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:45.988053+00:00
-- url     : https://prove2.me/submissions/52aea9e0-0356-400f-a7d4-f3443919e3c1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_d4l4_diff_flow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_flowDomainCriterion_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution : HolomorphicPeriodicityExtension (E := E) := by
  classical
  intro r X e he G hG m x hx hreal s hs
  have hdom : ∀ s' : X.Ψ → ℂ, X.flowV e s' x ∈ X.dom ↔ ∀ τ, 0 < 1 + (s' τ).im / X.ttV e x τ :=
    fun s' => (flowDomainCriterion_holds (E := E) r X e he x hx s').1
  set H : (X.Ψ → ℂ) → ℂ := fun s' =>
    G (X.flowV e s' x) - cexp (4 * Real.pi * I * ∑ τ, m τ * s' τ) * G x with hH

  suffices key : ∀ A : Finset X.Ψ, ∀ s' : X.Ψ → ℂ, (∀ τ ∉ A, (s' τ).im = 0) →
      X.flowV e s' x ∈ X.dom → H s' = 0 by
    exact sub_eq_zero.mp (key Finset.univ s (fun τ h => absurd (Finset.mem_univ τ) h) hs)
  intro A
  induction A using Finset.induction_on with
  | empty =>
    intro s' hs' _
    have hre : ∀ τ, (((s' τ).re : ℝ) : ℂ) = s' τ := fun τ =>
      Complex.ext (by simp) (by simp [hs' τ (by simp)])
    have h0 := hreal (fun τ => (s' τ).re)
    simp only [hre] at h0
    simp only [hH, h0, sub_self]
  | insert τ0 A hτ0 ih =>
    intro s' hs' hdom'
    have hcond := (hdom s').mp hdom'
    set V : Set ℂ := {z | 0 < 1 + z.im / X.ttV e x τ0} with hVdef
    have hVo : IsOpen V := isOpen_lt continuous_const (by fun_prop)
    have hVc : Convex ℝ V := by
      intro z hz w hw a b ha hb hab
      simp only [hVdef, Set.mem_setOf_eq] at hz hw ⊢
      have him : (a • z + b • w).im = a * z.im + b * w.im := by simp
      have h1 : 1 + (a * z.im + b * w.im) / X.ttV e x τ0 =
          a * (1 + z.im / X.ttV e x τ0) + b * (1 + w.im / X.ttV e x τ0) := by
        linear_combination (-1 : ℝ) * hab
      rw [him, h1]
      rcases ha.lt_or_eq with ha' | ha'
      · exact add_pos_of_pos_of_nonneg (mul_pos ha' hz) (mul_nonneg hb hw.le)
      · have hb1 : b = 1 := by linarith
        rw [← ha', hb1]
        simpa using hw
    have hreal0 : ∀ y : ℝ, (y : ℂ) ∈ V := by intro y; simp [hVdef]
    have hmaps : ∀ z ∈ V, X.flowV e (Function.update s' τ0 z) x ∈ X.dom := by
      intro z hz
      rw [hdom]
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa [hVdef] using hz
      · simpa [Function.update_of_ne h] using hcond τ
    have hu : ∀ τ, Differentiable ℂ (fun z : ℂ => Function.update s' τ0 z τ) := by
      intro τ
      by_cases h : τ = τ0
      · subst h
        simpa using differentiable_id
      · simpa [Function.update_of_ne h] using differentiable_const (s' τ)
    have hdiff : DifferentiableOn ℂ (fun z => H (Function.update s' τ0 z)) V := by
      have h1 : DifferentiableOn ℂ (fun z => G (X.flowV e (Function.update s' τ0 z) x)) V :=
        hG.comp (d4l4_diff_flow X e x s' τ0).differentiableOn (fun z hz => hmaps z hz)
      have hsum : Differentiable ℂ (fun z : ℂ => ∑ τ, m τ * Function.update s' τ0 z τ) := by
        intro z
        exact DifferentiableAt.fun_sum fun τ _ => ((hu τ) z).const_mul (m τ)
      have h2 : Differentiable ℂ (fun z : ℂ =>
          cexp (4 * Real.pi * I * ∑ τ, m τ * Function.update s' τ0 z τ) * G x) :=
        ((hsum.const_mul (4 * Real.pi * I)).cexp).mul_const (G x)
      exact h1.sub h2.differentiableOn
    have han : AnalyticOnNhd ℂ (fun z => H (Function.update s' τ0 z)) V :=
      hdiff.analyticOnNhd hVo

    have hzero_real : ∀ y : ℝ, H (Function.update s' τ0 (y : ℂ)) = 0 := by
      intro y
      apply ih
      · intro τ hτ
        by_cases h : τ = τ0
        · subst h
          simp
        · rw [Function.update_of_ne h]
          exact hs' τ (by simp [h, hτ])
      · exact hmaps _ (hreal0 y)
    have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), H (Function.update s' τ0 z) = 0 := by
      have ht : Filter.Tendsto (fun y : ℝ => (y : ℂ)) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℂ)) := by
        have h3 := Complex.continuous_ofReal.continuousWithinAt.tendsto_nhdsWithin
          (s := {(0 : ℝ)}ᶜ) (t := {(0 : ℂ)}ᶜ) (x := 0) (fun y hy => by simpa using hy)
        rwa [Complex.ofReal_zero] at h3
      exact ht.frequently (Filter.Eventually.frequently (Filter.Eventually.of_forall hzero_real))
    have h0V : (0 : ℂ) ∈ V := by simp [hVdef]
    have hEq := han.eqOn_zero_of_preconnected_of_frequently_eq_zero hVc.isPreconnected h0V hfreq
    have h4 := hEq (hcond τ0)
    simpa using h4
end ReciprocityTheory.ChartRestriction.G.FD
