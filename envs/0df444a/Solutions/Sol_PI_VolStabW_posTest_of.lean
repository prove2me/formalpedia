-- Prove2me | solution 1 for PI.VolStabW.posTest_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:21:26.704842+00:00
-- url     : https://prove2.me/submissions/a49a3443-5e23-4254-a150-0a3c3a873be2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosTest
import Theorems.Thm_PI_VolStabW_integrable_of_isOmT

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.VolFromSW
open scoped TensorProduct
namespace PI.VolStabW
theorem _root_.solution (hN : TestNear) : PosTest := by
  intro F E _ _ _ _ _ σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet ψ _hψ μ hμ νX hν μ' _hμ' hC
  obtain ⟨φ, hφ0, hadm, U, hUo, hUne, hUpos⟩ := hN F E σ hE M J hJ ha hc a ha1 ha2 X0 hT hdet
  refine ⟨φ, hφ0, hadm, fun hI0 => ?_⟩
  have hint : Integrable (fun X => (φ X : ℂ)) νX := integrable_of_isOmT hν hadm
  have hintR : Integrable φ νX := by simpa using hint.re
  have hI : ∫ X, φ X ∂νX = 0 := by
    rw [integral_complex_ofReal] at hI0
    exact_mod_cast hI0
  have hae : φ =ᵐ[νX] 0 := (integral_eq_zero_iff_of_nonneg (fun X => hφ0 X) hintR).1 hI
  obtain ⟨hnull, hform⟩ := hC
  classical
  let s : (Fin a → Fin M → AF F ⊗[F] E) → HA (AF F) σ J := fun y =>
    if h : ∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y then h.choose else 1
  have hs : ∀ y, (∃ g : HA (AF F) σ J, g • ratTup (AF F) X0 = y) →
      s y • ratTup (AF F) X0 = y := by
    intro y h
    simp only [s, dif_pos h]
    exact h.choose_spec
  have hf : Measurable (U.indicator (1 : HA (AF F) σ J → ENNReal)) :=
    measurable_one.indicator hUo.measurableSet
  have e := hform _ hf s hs
  have hL : ∫⁻ g, U.indicator (1 : HA (AF F) σ J → ENNReal) g ∂μ = μ U :=
    lintegral_indicator_one hUo.measurableSet
  have : μ.IsHaarMeasure := hμ
  have hpos : 0 < μ U := hUo.measure_pos μ hUne
  have hR : ∫⁻ y, ∫⁻ h', U.indicator (1 : HA (AF F) σ J → ENNReal)
      (s y * (h' : HA (AF F) σ J)) ∂μ' ∂νX = 0 := by
    refine (lintegral_congr_ae ?_).trans lintegral_zero
    filter_upwards [hae, ae_iff.2 hnull] with y hy0 hyo
    simp only [Pi.zero_apply] at hy0
    have hz : ∀ h' : stabT (AF F) σ J X0,
        U.indicator (1 : HA (AF F) σ J → ENNReal) (s y * (h' : HA (AF F) σ J)) = 0 := by
      intro h'
      refine Set.indicator_apply_eq_zero.2 fun hm => ?_
      exfalso
      have hh : (h' : HA (AF F) σ J) • ratTup (AF F) X0 = ratTup (AF F) X0 := h'.2
      have h0 := hUpos _ hm
      rw [mul_smul, hh, hs y hyo, hy0] at h0
      exact lt_irrefl _ h0
    simp only [hz, lintegral_zero]
  rw [hL, hR] at e
  exact hpos.ne' e
end PI.VolStabW
