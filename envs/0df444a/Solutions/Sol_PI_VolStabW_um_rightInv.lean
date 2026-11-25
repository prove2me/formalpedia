-- Prove2me | solution 1 for PI.VolStabW.um_rightInv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:35:23.191703+00:00
-- url     : https://prove2.me/submissions/b0824f5d-270d-4cf0-8df2-39c45f6879d6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Theorems.Thm_PI_VolStabW_um_eq_smul_of_sigmaCompact
import Theorems.Thm_PI_VolStabW_um_smulInv
import Theorems.Thm_PI_VolStabW_um_sigmaCompact

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
open MeasureTheory Measure Topology Set Function
open scoped Pointwise ENNReal NNReal
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [MeasurableSpace G] [BorelSpace G]
namespace PI.VolStabW
theorem _root_.solution (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [IsHaarMeasure μ]
    (𝓕 : Set G) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hfin : μ 𝓕 < ⊤) : IsMulRightInvariant μ := by
  have := um_sigmaCompact Γ μ 𝓕 h𝓕 hfin
  have := um_smulInv Γ μ
  have h0 : μ 𝓕 ≠ 0 := by
    intro h0
    have := h𝓕.measure_zero_of_invariant univ (fun g => smul_set_univ)
      (by rw [univ_inter]; exact h0)
    exact isOpen_univ.measure_ne_zero μ univ_nonempty this
  refine ⟨fun g => ?_⟩
  set c := haarScalarFactor (map (· * g) μ) μ with hcdef
  have hc : map (· * g) μ = c • μ := um_eq_smul_of_sigmaCompact _ _
  have hqmp : QuasiMeasurePreserving (· * g) μ μ :=
    ⟨measurable_mul_const g, by rw [hc]; exact smul_absolutelyContinuous⟩
  have h𝓕' : IsFundamentalDomain Γ ((· * g) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv hqmp (e := id) Function.bijective_id
      (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
  have hm : μ ((· * g) ⁻¹' 𝓕) = c * μ 𝓕 := by
    have : μ ((· * g) ⁻¹' 𝓕) = map (· * g) μ 𝓕 :=
      ((MeasurableEquiv.mulRight g).map_apply 𝓕).symm
    rw [this, hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcoe : (c : ℝ≥0∞) = 1 := by
    have := h𝓕'.measure_eq h𝓕
    rw [hm] at this
    rw [← ENNReal.mul_left_inj h0 hfin.ne, one_mul]
    exact this
  have hc1 : c = 1 := by exact_mod_cast hcoe
  rw [hc, hc1, one_smul]
end PI.VolStabW
