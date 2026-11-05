-- Prove2me | solution 1 for ResidualsDRO.Wass.theorem_7
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T11:32:56.508966+00:00
-- url     : https://prove2.me/submissions/a3b050bb-e80b-4962-b004-44c0e8d3a581

import Mathlib
import Definitions.Def_WassersteinDRO_Duality_worstCaseRisk
import Definitions.Def_ResidualsDRO_Wass_Setting
import Definitions.Def_ResidualsDRO_Wass_Radius
import Theorems.Thm_ResidualsDRO_Wass_theorem_7_display_3

open MeasureTheory ProbabilityTheory

namespace RDROW7Aux

open WassersteinDRO.Duality

theorem wass_symm_le {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] (p : ℝ) (hp : 0 ≤ p)
    (μ ν : Measure E) : wassersteinDistance p μ ν ≤ wassersteinDistance p ν μ := by
  unfold wassersteinDistance
  apply ENNReal.rpow_le_rpow _ (by positivity)
  refine le_iInf₂ fun π hπ => ?_
  refine (iInf₂_le (π.map (MeasurableEquiv.prodComm (α := E) (β := E))) ?_).trans ?_
  · constructor
    · rw [Measure.map_map measurable_fst (MeasurableEquiv.measurable _)]
      have e : (Prod.fst ∘ ⇑(MeasurableEquiv.prodComm (α := E) (β := E))) = Prod.snd := rfl
      rw [e]; exact hπ.2
    · rw [Measure.map_map measurable_snd (MeasurableEquiv.measurable _)]
      have e : (Prod.snd ∘ ⇑(MeasurableEquiv.prodComm (α := E) (β := E))) = Prod.fst := rfl
      rw [e]; exact hπ.1
  · rw [lintegral_map_equiv]
    apply le_of_eq
    congr 1
    funext z
    simp [MeasurableEquiv.prodComm, norm_sub_rev]

end RDROW7Aux

open ResidualsDRO.Wass in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {dx dy dz n : ℕ} (hdy : 1 ≤ dy) (hn : 1 ≤ n)
    (p a : ℝ) (hp : 1 ≤ p) (hpdy : p ≠ (dy : ℝ) / 2)
    (𝒴 : Set (EuclideanSpace ℝ (Fin dy)))
    (h𝒴c : IsClosed 𝒴) (h𝒴v : Convex ℝ 𝒴) (h𝒴n : 𝒴.Nonempty)
    (proj : EuclideanSpace ℝ (Fin dy) → EuclideanSpace ℝ (Fin dy))
    (hproj : IsNearestPointProj 𝒴 proj)
    (Pε : Measure (EuclideanSpace ℝ (Fin dy))) [IsProbabilityMeasure Pε]
    (hA1 : Assumption1 Pε p a)
    (fstar : EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (fhat : Ω → EuclideanSpace ℝ (Fin dx) → EuclideanSpace ℝ (Fin dy))
    (xs : Fin n → Ω → EuclideanSpace ℝ (Fin dx))
    (eps : Fin n → Ω → EuclideanSpace ℝ (Fin dy)) (heps_meas : ∀ i, Measurable (eps i))
    (heps_indep : iIndepFun eps P) (heps_law : ∀ i, P.map (eps i) = Pε)
    (x : EuclideanSpace ℝ (Fin dx)) (hY : ∀ i ω, fstar x + eps i ω ∈ 𝒴)
    (hsupp : condLaw Pε fstar x 𝒴ᶜ = 0)
    (κ : ℝ → ℝ) (hA2 : Assumption2 P fstar fhat xs p x κ)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hL2 : Lemma2Bound P Pε fstar eps x dy p a c₁ c₂)
    (𝒵 : Set (EuclideanSpace ℝ (Fin dz))) (h𝒵c : IsCompact 𝒵) (h𝒵n : 𝒵.Nonempty)
    (c : EuclideanSpace ℝ (Fin dz) → EuclideanSpace ℝ (Fin dy) → ℝ)
    (hc_meas : ∀ z, Measurable (c z))
    (hc_int : ∀ z ∈ 𝒵, Integrable (fun e => c z (fstar x + e)) Pε)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (zhat : Ω → EuclideanSpace ℝ (Fin dz))
    (hopt : ∀ ω, zhat ω ∈ 𝒵 ∧ ∀ z ∈ 𝒵,
      WassersteinDRO.Duality.worstCaseRisk (radius κ c₁ c₂ a p dy n α) p 𝒴
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x) (c (zhat ω)) ≤
        WassersteinDRO.Duality.worstCaseRisk (radius κ c₁ c₂ a p dy n α) p 𝒴
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x) (c z)) :
    P {ω | ¬ ((trueObjective Pε fstar c x (zhat ω) : EReal) ≤
        erDROValue 𝒵 c (radius κ c₁ c₂ a p dy n α) p 𝒴
          (erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x))} ≤
      ENNReal.ofReal α := by
  refine le_trans (measure_mono ?_) (theorem_7_display_3 P hdy hn p a hp hpdy 𝒴 h𝒴c h𝒴v h𝒴n proj
    hproj Pε hA1 fstar fhat xs eps heps_meas heps_indep heps_law x hY κ hA2 c₁ c₂ hc₁ hc₂ hL2
    α hα0 hα1)
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  by_contra hc
  push Not at hc
  apply hω
  set PER := erEmpirical proj fstar (fhat ω) (fun i => xs i ω) (fun i => eps i ω) x
  set ζ := radius κ c₁ c₂ a p dy n α
  set Q := condLaw Pε fstar x
  have hmeas : Measurable (fun e : EuclideanSpace ℝ (Fin dy) => fstar x + e) :=
    measurable_const.add measurable_id
  have hQprob : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map hmeas.aemeasurable
  have hmem : Q ∈ WassersteinDRO.Duality.ambiguitySet ζ p 𝒴 PER := by
    refine ⟨measure_univ, hsupp, ?_⟩
    exact (RDROW7Aux.wass_symm_le p (by linarith) Q PER).trans hc
  obtain ⟨hz, hopt'⟩ := hopt ω
  have hint : Integrable (c (zhat ω)) Q := by
    rw [show Q = Pε.map (fun e => fstar x + e) from rfl]
    rw [integrable_map_measure (hc_meas _).aestronglyMeasurable hmeas.aemeasurable]
    exact hc_int _ hz
  have hval : (trueObjective Pε fstar c x (zhat ω) : EReal) =
      (WassersteinDRO.Duality.nominalRisk Q (c (zhat ω)) : EReal) := by
    unfold WassersteinDRO.Duality.nominalRisk trueObjective
    congr 1
    rw [show Q = Pε.map (fun e => fstar x + e) from rfl]
    rw [integral_map hmeas.aemeasurable (hc_meas _).aestronglyMeasurable]
  rw [hval]
  unfold erDROValue
  refine le_iInf₂ fun z hz' => le_trans ?_ (hopt' z hz')
  unfold WassersteinDRO.Duality.worstCaseRisk
  exact le_iSup_of_le Q (le_iSup_of_le hmem (le_iSup_of_le hint le_rfl))
