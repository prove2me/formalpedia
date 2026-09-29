-- Prove2me | solution 1 for UnramifiedWhittaker.integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/37d3c3bb-2a3b-5ff1-b0d5-ce153c291835

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_BoundedGenuineCuspRealization
import Definitions.Def_NumberField_IdeleProductMeasure
import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_NumberField_AdelicFourier
import Theorems.Thm_NumberField_TateGlobal_continuous_ideleNorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker

open NumberField NumberField.AdelicLevel NumberField.AdelicBox NumberField.AdelicHaar MeasureTheory
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering
open IsDedekindDomain NumberField.TateGlobal
open UnramifiedWhittaker NumberField.Idele

attribute [local instance] NumberField.Idele.ideleBorel NumberField.Idele.borelSpace_ideleBorel

namespace C6D

theorem rpow_le_of_pinched {t Q x B : ℝ} (ht : 0 < t) (hQ1 : 1 ≤ Q) (htQ : t ≤ Q) (htQ' : t⁻¹ ≤ Q)
    (hx : |x| ≤ B) : t ^ x ≤ Q ^ B := by
  rcases le_or_gt 0 x with h | h
  · calc t ^ x ≤ Q ^ x := Real.rpow_le_rpow ht.le htQ h
      _ ≤ Q ^ B := Real.rpow_le_rpow_of_exponent_le hQ1 ((le_abs_self x).trans hx)
  · have : t ^ x = t⁻¹ ^ (-x) := by
      rw [Real.inv_rpow ht.le, Real.rpow_neg ht.le, inv_inv]
    rw [this]
    calc t⁻¹ ^ (-x) ≤ Q ^ (-x) := Real.rpow_le_rpow (inv_nonneg.mpr ht.le) htQ' (by linarith)
      _ ≤ Q ^ B := Real.rpow_le_rpow_of_exponent_le hQ1 ((neg_le_abs x).trans hx)

theorem abs_log_le_of_pinched {t Q : ℝ} (ht : 0 < t) (htQ : t ≤ Q) (htQ' : t⁻¹ ≤ Q) :
    |Real.log t| ≤ Real.log Q := by
  rw [abs_le]
  constructor
  · have := Real.log_le_log (inv_pos.mpr ht) htQ'
    rw [Real.log_inv] at this
    linarith
  · exact Real.log_le_log ht htQ

variable (F : Type) [Field F] [NumberField F]

end C6D

theorem solution
    (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F)))
    (Wg : AdelicGL2 (𝓞 F) F → ℂ) (χ : (AdeleRing (𝓞 F) F)ˣ →* ℂˣ)
    (μ : (AdeleRing (𝓞 F) F)ˣ → ℝ)
    (Ω K : Set (AdeleRing (𝓞 F) F)ˣ) (hΩm : MeasurableSet[NumberField.Idele.ideleBorel F] Ω) (hKm : MeasurableSet[NumberField.Idele.ideleBorel F] K)
    (hΩ : NumberField.Idele.sPartMeasure F S Ωᶜ = 0) (hK : NumberField.Idele.sPartMeasure F S K < ⊤)
    (M₀ M₁ X r R : ℝ) (hr : 0 < r)
    (hmeas : ∀ s : ℂ, Measurable[NumberField.Idele.ideleBorel F] fun a => (μ a : ℂ) * zetaIntegrand Wg χ s a)
    (hμ : ∀ a, |μ a| ≤ M₀)
    (hsupp : ∀ a ∈ Ω, a ∉ K → μ a = 0)
    (hKb : ∀ a ∈ K, ‖Wg (diagOne a)‖ ≤ M₁ ∧ ‖((χ a : ℂˣ) : ℂ)‖ ≤ X ∧ r ≤ ideleNorm F a ∧ ideleNorm F a ≤ R) :
    (∀ s : ℂ, Integrable (fun a => (μ a : ℂ) * zetaIntegrand Wg χ s a) (NumberField.Idele.sPartMeasure F S)) ∧
    Differentiable ℂ (fun s : ℂ => ∫ a, (μ a : ℂ) * zetaIntegrand Wg χ s a ∂(NumberField.Idele.sPartMeasure F S)) := by
  set ν := sPartMeasure F S with hν
  set Q : ℝ := max (max r⁻¹ R) 1 with hQ
  have hQ1 : 1 ≤ Q := le_max_right _ _
  have hpin : ∀ a ∈ K, 0 < ideleNorm F a ∧ ideleNorm F a ≤ Q ∧ (ideleNorm F a)⁻¹ ≤ Q := by
    intro a ha
    obtain ⟨-, -, h1, h2⟩ := hKb a ha
    refine ⟨ideleNorm_pos _, h2.trans ((le_max_right _ _).trans (le_max_left _ _)), ?_⟩
    calc (ideleNorm F a)⁻¹ ≤ r⁻¹ := by gcongr
      _ ≤ Q := (le_max_left _ _).trans (le_max_left _ _)
  have hM₀ : 0 ≤ M₀ := (abs_nonneg _).trans (hμ 1)
  have hae : ∀ᵐ a ∂ν, a ∈ Ω := by
    rw [ae_iff]; exact hΩ

  have hpt : ∀ (s : ℂ) (Bx : ℝ), |s.re - 1| ≤ Bx → ∀ a, a ∈ Ω →
      ‖(μ a : ℂ) * zetaIntegrand Wg χ s a‖ ≤ K.indicator (fun _ => M₀ * M₁ * X * Q ^ Bx) a := by
    intro s Bx hs a haΩ
    by_cases haK : a ∈ K
    · rw [Set.indicator_of_mem haK]
      obtain ⟨hW, hχa, -, -⟩ := hKb a haK
      obtain ⟨htpos, htQ, htQ'⟩ := hpin a haK
      simp only [zetaIntegrand, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hcp : ‖((ideleNorm F a : ℝ) : ℂ) ^ (s - 1)‖ ≤ Q ^ Bx := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.sub_re, Complex.one_re]
        exact C6D.rpow_le_of_pinched htpos hQ1 htQ htQ' hs
      have hM₁ : 0 ≤ M₁ := (norm_nonneg _).trans hW
      have hX : 0 ≤ X := (norm_nonneg _).trans hχa
      have hMX : 0 ≤ M₁ * X := mul_nonneg hM₁ hX
      calc |μ a| * (‖Wg (diagOne a)‖ * ‖((χ a : ℂˣ) : ℂ)‖ * ‖((ideleNorm F a : ℝ) : ℂ) ^ (s - 1)‖)
          ≤ M₀ * (M₁ * X * Q ^ Bx) := by gcongr; exact hμ a
        _ = M₀ * M₁ * X * Q ^ Bx := by ring
    · rw [Set.indicator_of_notMem haK, hsupp a haΩ haK]
      simp
  have hint : ∀ s : ℂ, Integrable (fun a => (μ a : ℂ) * zetaIntegrand Wg χ s a) ν := by
    intro s
    refine Integrable.mono' ((integrableOn_const (hs := hK.ne) (C := M₀ * M₁ * X * Q ^ |s.re - 1|)).integrable_indicator hKm)
      (hmeas s).aestronglyMeasurable (hae.mono fun a ha => hpt s _ le_rfl a ha)
  refine ⟨hint, fun s₀ => ?_⟩

  set F' : ℂ → (AdeleRing (𝓞 F) F)ˣ → ℂ := fun s a =>
    (μ a : ℂ) * zetaIntegrand Wg χ s a * (Real.log (ideleNorm F a) : ℂ) with hF'
  have hderiv : ∀ (a : (AdeleRing (𝓞 F) F)ˣ) (s : ℂ),
      HasDerivAt (fun s => (μ a : ℂ) * zetaIntegrand Wg χ s a) (F' s a) s := by
    intro a s
    have htpos := ideleNorm_pos (F := F) a
    have ht : ((ideleNorm F a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
    have h1 : HasDerivAt (fun s : ℂ => ((ideleNorm F a : ℝ) : ℂ) ^ (s - 1))
        (((ideleNorm F a : ℝ) : ℂ) ^ (s - 1) * Complex.log ((ideleNorm F a : ℝ) : ℂ) * 1) s :=
      ((hasDerivAt_id s).sub_const 1).const_cpow (Or.inl ht)
    have h2 := h1.const_mul ((μ a : ℂ) * (Wg (diagOne a) * ((χ a : ℂˣ) : ℂ)))
    rw [← Complex.ofReal_log htpos.le] at h2
    simp only [hF', zetaIntegrand]
    convert h2 using 1 <;> try with_reducible_and_instances rfl
    · funext s; ring
    · ring
  have hBx : ∀ s ∈ Metric.ball s₀ 1, |s.re - 1| ≤ |s₀.re - 1| + 1 := by
    intro s hs
    have h := Complex.abs_re_le_norm (s - s₀)
    rw [Complex.sub_re] at h
    have h' : ‖s - s₀‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hs
    have := abs_sub_abs_le_abs_sub (s.re - 1) (s₀.re - 1)
    rw [show s.re - 1 - (s₀.re - 1) = s.re - s₀.re by ring] at this
    linarith
  have hbound : ∀ᵐ a ∂ν, ∀ s ∈ Metric.ball s₀ 1,
      ‖F' s a‖ ≤ K.indicator (fun _ => M₀ * M₁ * X * Q ^ (|s₀.re - 1| + 1) * Real.log Q) a := by
    refine hae.mono fun a haΩ s hs => ?_
    have hp := hpt s _ (hBx s hs) a haΩ
    simp only [hF', norm_mul]
    by_cases haK : a ∈ K
    · rw [Set.indicator_of_mem haK] at hp ⊢
      obtain ⟨htpos, htQ, htQ'⟩ := hpin a haK
      have hl : ‖(Real.log (ideleNorm F a) : ℂ)‖ ≤ Real.log Q := by
        rw [Complex.norm_real, Real.norm_eq_abs]
        exact C6D.abs_log_le_of_pinched htpos htQ htQ'
      have hc : 0 ≤ M₀ * M₁ * X * Q ^ (|s₀.re - 1| + 1) := le_trans (norm_nonneg _) hp
      simp only [norm_mul] at hp
      exact mul_le_mul hp hl (norm_nonneg _) hc
    · rw [Set.indicator_of_notMem haK] at hp ⊢
      have : ‖(μ a : ℂ) * zetaIntegrand Wg χ s a‖ = 0 := le_antisymm hp (norm_nonneg _)
      rw [norm_mul] at this
      rw [this, zero_mul]
  have hF'meas : AEStronglyMeasurable (F' s₀) ν := by
    have hl : Measurable fun a : (AdeleRing (𝓞 F) F)ˣ => (Real.log (ideleNorm F a) : ℂ) :=
      Complex.measurable_ofReal.comp (Real.measurable_log.comp
        (NumberField.TateGlobal.continuous_ideleNorm F).measurable)
    exact ((hmeas s₀).mul hl).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν)
    (F := fun (s : ℂ) (a : (AdeleRing (𝓞 F) F)ˣ) => (μ a : ℂ) * zetaIntegrand Wg χ s a)
    (F' := F') (x₀ := s₀) (s := Metric.ball s₀ 1)
    (bound := K.indicator (fun _ => M₀ * M₁ * X * Q ^ (|s₀.re - 1| + 1) * Real.log Q))
    (Metric.ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s => (hmeas s).aestronglyMeasurable)
    (hint s₀) hF'meas hbound
    ((integrableOn_const (hs := hK.ne)).integrable_indicator hKm)
    (ae_of_all _ fun a s _ => hderiv a s)
  exact key.2.differentiableAt

end S_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded
end P2MW
export P2MW.S_UnramifiedWhittaker_integrable_and_differentiable_integral_mul_zetaIntegrand_sPartMeasure_of_bounded (solution)
