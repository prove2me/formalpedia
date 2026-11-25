-- Prove2me | solution 1 for PI.VolStabW.SdUniqW.eq_of_testEx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:10.834279+00:00
-- url     : https://prove2.me/submissions/f3a9cc23-7d34-4250-8de6-494e8f76f113

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq

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
open PI.VolStabW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
namespace PI.VolStabW.SdUniqW
theorem _root_.solution {V : Type} [AddCommGroup V] [TopologicalSpace V]
    [IsTopologicalAddGroup V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [MeasurableSpace V] [BorelSpace V] {μ ν : Measure V} {χ : V → V → ℂ}
    (hμ : SelfDual μ χ) (hν : SelfDual ν χ) (hT : TestEx μ χ) : μ = ν := by
  unfold SelfDual at hμ hν
  obtain ⟨hμH, hμI⟩ := hμ
  obtain ⟨hνH, hνI⟩ := hν
  obtain ⟨Φ, hc, hs, hi, z, hz⟩ := hT
  obtain ⟨c, rfl⟩ : ∃ c : NNReal, ν = c • μ := by
    first
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul ν μ⟩
    | exact ⟨_, Measure.isAddHaarMeasure_eq_smul_of_regular ν μ⟩
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_regular ν μ⟩
    | exact ⟨_, Measure.isAddLeftInvariant_eq_smul_of_innerRegular ν μ⟩
  have h1 := hμI Φ hc hs hi z
  have hi' : Integrable (fun y => ∫ x, Φ x * χ x y ∂(c • μ)) (c • μ) := by
    simp only [integral_smul_nnreal_measure, NNReal.smul_def]
    exact (hi.smul (c : ℝ)).smul_measure_nnreal
  have h2 := hνI Φ hc hs hi' z
  simp_rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_mul_assoc, integral_smul, h1,
    smul_smul] at h2
  have h3 : ((c : ℝ) * c - 1) • Φ (-z) = 0 := by rw [sub_smul, one_smul, h2, sub_self]
  rcases smul_eq_zero.1 h3 with h | h
  · have hx : (c : ℝ) = 1 := by
      rcases mul_self_eq_one_iff.1 (sub_eq_zero.1 h) with h' | h'
      · exact h'
      · linarith [c.2]
    have hc1 : c = 1 := by exact_mod_cast hx
    rw [hc1, one_smul]
  · exact absurd h hz
end PI.VolStabW.SdUniqW
