-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLatSection_proof_a1a554adc1f2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:53:03.4168+00:00
-- url     : https://prove2.me/submissions/24b2de26-7981-4895-a1c5-5c225dc8619f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_PChartLatSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_form_mem_iff_6b464eb5ceeb
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_eq_zero_of_mem_a3afea90a62b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_aeval_chartMonomial_165324199dda
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_coord_notMem_iff_c1ab93abd3c8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChartLatSection_exists_chartForm_22a5052f5383
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_exists_chart_5599c818fd08
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ArithVariety_mkF_eq_zero_iff_91580b64c057
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IntegralSection_value_mem_chartLat_a828c5da8776
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_chart_3cad6f9af78e


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ReciprocityTheory.ChartRestriction.G
noncomputable section
open ChartLatSection
namespace GroundTheory.Heights₂.Heights
namespace ChartLatSection
theorem _root_.solution : ChartLatSection.Statement := by
  intro ι _ _ n Ω _ y P a τ s hP
  constructor
  · intro hs
    obtain ⟨c₀, hc₀⟩ := P.exists_chart
    have hy₀ : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc₀ k)
    obtain ⟨d₀, δ₀, e₀, he₀, hδ₀, hv₀⟩ := exists_chartForm y a τ hs c₀ hy₀
    have hm₀ : ∏ k, y ⟨k, c₀ k⟩ ^ d₀ k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hy₀ k)
    have hden : chartMonomial c₀ d₀ ∉ P.ideal := by
      rw [hP, form_mem_iff y (isWeightedHomogeneous_chartMonomial c₀ d₀), aeval_chartMonomial]
      exact hm₀
    refine ⟨⟨e₀, chartMonomial c₀ d₀, δ₀, d₀, he₀, isWeightedHomogeneous_chartMonomial c₀ d₀,
      fun k => by rw [hδ₀ k]; ring, hden, fun c hc => ?_⟩, ?_⟩
    · have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (coord_notMem_iff y hP _).mp (hc k)
      obtain ⟨d, δ, e, he, hδ, hv⟩ := exists_chartForm y a τ hs c hyc
      refine ⟨d, e, ⟨δ, he, hδ⟩, ?_⟩
      have hdeg : d₀ + δ = δ₀ + d := by
        funext k
        have h1 := hδ k
        have h2 := hδ₀ k
        simp only [Pi.add_apply]
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n)
          (chartMonomial c₀ d₀ * e - e₀ * chartMonomial c d) (d₀ + δ) := by
        refine ((isWeightedHomogeneous_chartMonomial c₀ d₀).mul he).sub ?_
        rw [hdeg]
        exact he₀.mul (isWeightedHomogeneous_chartMonomial c d)
      rw [hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv, hv₀, aeval_chartMonomial,
        aeval_chartMonomial]
      ring
    · intro g h δg δh hg hh hd
      have hmk : P.mkF (chartMonomial c₀ d₀) ≠ 0 := by
        rw [Ne, P.mkF_eq_zero_iff]
        exact hden
      have hdeg : δg + d₀ = δ₀ + δh := by
        funext k
        have h1 := hd k
        have h2 := hδ₀ k
        simp only [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] at h1 h2 ⊢
        omega
      have hhom : IsWeightedHomogeneous (coordDeg n) (g * chartMonomial c₀ d₀ - e₀ * h) (δg + d₀) := by
        refine (hg.mul (isWeightedHomogeneous_chartMonomial c₀ d₀)).sub ?_
        rw [hdeg]
        exact he₀.mul hh
      have key : P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h ↔
          g * chartMonomial c₀ d₀ - e₀ * h ∈ P.ideal := by
        rw [← P.mkF_eq_zero_iff, map_sub, map_mul, map_mul, sub_eq_zero, div_mul_eq_mul_div,
          eq_div_iff hmk]
      show _ ↔ P.mkF g = P.mkF e₀ / P.mkF (chartMonomial c₀ d₀) * P.mkF h
      rw [key, hP, form_mem_iff y hhom, map_sub, map_mul, map_mul, hv₀, aeval_chartMonomial,
        sub_eq_zero]
      constructor
      · intro h1
        rw [h1]
        ring
      · intro h1
        apply mul_right_cancel₀ hm₀
        linear_combination h1
  · rintro ⟨t, ht⟩
    have hyP : ∀ f ∈ P.ideal, aeval y f = 0 := fun f hf => aeval_eq_zero_of_mem y (hP ▸ hf)
    have hG : aeval y t.den ≠ 0 := by
      intro h0
      exact t.den_not_mem (by rw [hP, form_mem_iff y t.den_isHomogeneous]; exact h0)
    have hmk : P.mkF t.den ≠ 0 := by
      rw [Ne, P.mkF_eq_zero_iff]
      exact t.den_not_mem
    have hread : aeval y t.num = s * aeval y t.den := by
      refine (ht t.num t.den t.numDeg t.denDeg t.num_isHomogeneous t.den_isHomogeneous
        (fun k => by have := t.deg_eq k; linarith)).mpr ?_
      show P.mkF t.num = P.mkF t.num / P.mkF t.den * P.mkF t.den
      rw [div_mul_cancel₀ _ hmk]
    have hs : s = aeval y t.num / aeval y t.den := by
      rw [hread, mul_div_assoc, div_self hG, mul_one]
    have hmem := t.value_mem_chartLat y hyP hG
    rw [← hs] at hmem
    intro c hc
    have h := hmem c hc
    have he : ∀ k, -(((1 : ℕ) : ℤ) * (τ • a) k) = -((τ : ℤ) * a k) := fun k => by
      simp
    simp only [he] at h
    exact h
end ChartLatSection
end GroundTheory.Heights₂.Heights
