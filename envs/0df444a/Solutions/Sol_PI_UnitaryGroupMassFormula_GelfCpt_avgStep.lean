-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.GelfCpt.avgStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:03:24.858433+00:00
-- url     : https://prove2.me/submissions/9b04ffa0-904e-489f-b612-01c6720c0eee

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UMultOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_AvgStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_CompactGelfandAverage_MulIntMatMul
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_integrable_of_cont
import Theorems.Thm_PI_UnitaryGroupMassFormula_GelfCpt_intMat_conj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.GelfCpt
open MeasureTheory Matrix
namespace PI.UnitaryGroupMassFormula.GelfCpt
theorem _root_.solution : AvgStep := by
  intro G _ _ _ _ _ _ _ _ μ _ H hH N ρ hc f hf hA
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  letI : MeasurableSpace H := borel H
  haveI : BorelSpace H := ⟨rfl⟩
  let ν : Measure H := Measure.haarMeasure ⊤
  haveI : IsProbabilityMeasure ν := ⟨by
    have := Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts H))
    rwa [TopologicalSpace.PositiveCompacts.coe_top] at this⟩
  have hF : Continuous (Function.uncurry fun (g : G) (h : H) => f ((h : G)⁻¹ * g * h)) :=
    hf.comp (((continuous_subtype_val.comp continuous_snd).inv.mul continuous_fst).mul
      (continuous_subtype_val.comp continuous_snd))
  refine ⟨fun g => ∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν, ?_, ?_, ?_⟩
  · have := continuous_parametric_integral_of_continuous (μ := ν) hF isCompact_univ
    simpa only [Measure.restrict_univ] using this
  · intro k hk x
    show ∫ h : H, f ((h : G)⁻¹ * (k * x * k⁻¹) * h) ∂ν = ∫ h : H, f ((h : G)⁻¹ * x * h) ∂ν
    have e := integral_mul_left_eq_self (μ := ν) (fun h : H => f ((h : G)⁻¹ * x * h))
      (⟨k, hk⟩⁻¹ : H)
    rw [← e]
    congr 1
    funext h
    show f ((h : G)⁻¹ * (k * x * k⁻¹) * h) = f (((⟨k, hk⟩⁻¹ * h : H) : G)⁻¹ * x * ((⟨k, hk⟩⁻¹ * h : H) : G))
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  · ext i j
    have hR : Continuous fun g => ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j :=
      (continuous_apply j).comp ((continuous_apply i).comp hc)
    have hI : Integrable (Function.uncurry fun (g : G) (h : H) =>
        f ((h : G)⁻¹ * g * h) * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j)
        (μ.prod ν) :=
      integrable_of_cont _ (hF.mul (hR.comp continuous_fst))
    simp only [intMat, Matrix.of_apply]
    calc ∫ g, (∫ h : H, f ((h : G)⁻¹ * g * h) ∂ν) *
          ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ
        = ∫ g, ∫ h : H, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂ν ∂μ := by
          congr 1; funext g; rw [integral_mul_const]
      _ = ∫ h : H, ∫ g, f ((h : G)⁻¹ * g * h) *
            ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ ∂ν :=
          integral_integral_swap hI
      _ = ∫ _h : H, intMat μ ρ f i j ∂ν := by
          congr 1; funext h
          exact intMat_conj μ ρ hc hf (h : G) (hA h h.2) i j
      _ = ∫ g, f g * ((ρ g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) i j ∂μ := by
          simp [intMat]
end PI.UnitaryGroupMassFormula.GelfCpt
