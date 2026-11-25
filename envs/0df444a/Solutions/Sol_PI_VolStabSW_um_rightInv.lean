-- Prove2me | solution 1 for PI.VolStabSW.um_rightInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:53:33.93599+00:00
-- url     : https://prove2.me/submissions/1eaeaa1f-8d07-46fe-8538-170a595da14f

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_FibInfEx
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_Unimod
import Theorems.Thm_PI_VolStabSW_um_eq_smul_of_sigmaCompact
import Theorems.Thm_PI_VolStabSW_um_smulInv
import Theorems.Thm_PI_VolStabSW_um_sigmaCompact

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
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabSW
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [IsHaarMeasure μ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) : IsMulRightInvariant μ := by
  haveI := um_sigmaCompact Γ μ 𝓕 h𝓕 hfin
  haveI : SMulInvariantMeasure Γ G μ := um_smulInv Γ μ
  refine ⟨fun g => ?_⟩
  haveI : IsMulLeftInvariant (map (· * g) μ) := inferInstance
  haveI : IsFiniteMeasureOnCompacts (map (· * g) μ) := by
    refine ⟨fun K hK => ?_⟩
    rw [map_apply (measurable_mul_const g) hK.measurableSet]
    exact ((Homeomorph.mulRight g).isCompact_preimage.2 hK).measure_lt_top
  have hc := um_eq_smul_of_sigmaCompact (map (· * g) μ) μ
  have h𝓕' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv ⟨measurable_mul_const g, by rw [hc]; exact Measure.smul_absolutelyContinuous⟩
      Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have heq : μ ((· * g) ⁻¹' 𝓕) = μ 𝓕 := h𝓕'.measure_eq h𝓕
  have h1 := (MeasurableEquiv.mulRight g).map_apply (μ := μ) 𝓕
  simp only [MeasurableEquiv.coe_mulRight] at h1
  have hne : μ 𝓕 ≠ 0 := h𝓕.measure_ne_zero (NeZero.ne μ)
  have e := congrArg (fun ν : Measure G => ν 𝓕) hc
  simp only [h1, heq, Measure.nnreal_smul_coe_apply] at e
  have hc1 : haarScalarFactor (map (· * g) μ) μ = 1 := by
    have e2 := (ENNReal.mul_left_inj hne hfin.ne).1 (e.symm.trans (one_mul _).symm)
    exact ENNReal.coe_eq_one.1 e2
  rw [hc, hc1, one_smul]
end PI.VolStabSW
