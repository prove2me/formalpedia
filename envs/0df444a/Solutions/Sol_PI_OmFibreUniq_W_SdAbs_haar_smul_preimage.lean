-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdAbs.haar_smul_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:52.518601+00:00
-- url     : https://prove2.me/submissions/2bd299e1-ff99-43a2-8f33-053df255b881

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SmulMemHermR
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExAbs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdAbs
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
open PI.VolStabSW.SdUniqW PI.OmFibreUniq.W.SdCore PI.OmFibreUniq.W.SdChar
open scoped ENNReal
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  {V : Type} [AddCommGroup V] [Module (Fv F v) V] [TopologicalSpace V]
  [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V] [LocallyCompactSpace V]
  [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V] (B : V → V → Fv F v)
namespace PI.OmFibreUniq.W.SdAbs
theorem _root_.solution (μ0 : Measure V) [μ0.IsAddHaarMeasure] (a : Fv F v) (ha : a ≠ 0) :
    ∃ c : ℝ≥0∞, ∀ S, MeasurableSet S → μ0 ((fun y : V => a • y) ⁻¹' S) = c * μ0 S := by
  let e : V ≃+ V := (LinearEquiv.smulOfNeZero (Fv F v) V a ha).toAddEquiv
  have he : Continuous e := by
    show Continuous fun y : V => a • y
    exact continuous_const_smul a
  have hes : Continuous e.symm := by
    show Continuous fun y : V => a⁻¹ • y
    exact continuous_const_smul a⁻¹
  haveI := AddEquiv.isAddHaarMeasure_map μ0 e he hes
  refine ⟨(Measure.addHaarScalarFactor (μ0.map e) μ0 : ℝ≥0∞), fun S hS => ?_⟩
  have hmap : μ0.map e = Measure.addHaarScalarFactor (μ0.map e) μ0 • μ0 :=
    Measure.isAddLeftInvariant_eq_smul _ _
  have h := Measure.map_apply (μ := μ0) he.measurable hS
  rw [hmap, Measure.smul_apply] at h
  show μ0 (e ⁻¹' S) = _
  rw [← h]
  rfl
end PI.OmFibreUniq.W.SdAbs
