-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.eq_of_testEx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:54:10.499489+00:00
-- url     : https://prove2.me/submissions/c8d3ccb7-5787-4563-921b-e2bd65bc2a8c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ ν : Measure V} {χ : V → V → ℂ}
    (hμ : SelfDual μ χ) (hν : SelfDual ν χ) (hT : TestEx μ χ) : μ = ν := by
  obtain ⟨hμH, hμD⟩ := hμ
  obtain ⟨hνH, hνD⟩ := hν
  obtain ⟨Φ, hc, hs, hi, z, hz⟩ := hT
  have hνeq : ν = ((Measure.addHaarScalarFactor ν μ : NNReal) : ENNReal) • μ :=
    (Measure.isAddLeftInvariant_eq_smul ν μ).trans (ENNReal.smul_def _ _)
  generalize hcdef : ((Measure.addHaarScalarFactor ν μ : NNReal) : ENNReal) = c at hνeq
  have hcT : c ≠ ⊤ := by rw [← hcdef]; exact ENNReal.coe_ne_top
  subst hνeq
  have htr : ∀ y, ∫ x, Φ x * χ x y ∂(c • μ) = c.toReal • ∫ x, Φ x * χ x y ∂μ :=
    fun y => integral_smul_measure _ _
  have hiν : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ) := by
    simp_rw [htr]
    exact (hi.smul c.toReal).smul_measure hcT
  have e1 := hμD Φ hc hs hi z
  have e2 := hνD Φ hc hs hiν z
  rw [integral_smul_measure] at e2
  simp_rw [htr, smul_mul_assoc, integral_smul, e1] at e2
  have hr : c.toReal * c.toReal = 1 := by
    rw [smul_smul, Complex.real_smul] at e2
    have h3 : ((c.toReal * c.toReal : ℝ) : ℂ) = 1 := mul_right_cancel₀ hz (e2.trans (one_mul _).symm)
    exact_mod_cast h3
  have hr1 : c.toReal = 1 := by
    have hpos : 0 ≤ c.toReal := ENNReal.toReal_nonneg
    nlinarith
  rw [(ENNReal.toReal_eq_one_iff c).mp hr1, one_smul]
end PI.VolStabSW.SdUniqW
