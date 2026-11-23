-- Prove2me | solution 1 for PI.VolStabW.us_invInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:19.265456+00:00
-- url     : https://prove2.me/submissions/3a785b54-85d6-4192-973c-6e16c44bb2ed

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_VolStabFromSWW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_Unimod
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_InvInvSt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_UnimodStab
import Theorems.Thm_PI_VolStabW_us_exists_open
import Theorems.Thm_PI_VolStabW_um_eq_smul_of_sigmaCompact


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
theorem _root_.solution [SigmaCompactSpace G] (μ : Measure G) [IsHaarMeasure μ]
    [IsMulRightInvariant μ] : IsInvInvariant μ := by
  have hc : μ.inv = haarScalarFactor μ.inv μ • μ := um_eq_smul_of_sigmaCompact _ _
  obtain ⟨U, hUo, -, hUi, hpos, hfin⟩ := us_exists_open μ
  have h : μ.inv U = μ U := by rw [Measure.inv_apply, hUi]
  rw [hc, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h
  have hc1 : haarScalarFactor μ.inv μ = 1 := by
    have : ((haarScalarFactor μ.inv μ : ℝ≥0) : ℝ≥0∞) = 1 := by
      rw [← ENNReal.mul_left_inj hpos.ne' hfin.ne, one_mul]
      exact h
    exact_mod_cast this
  exact ⟨by rw [hc, hc1, one_smul]⟩
end PI.VolStabW
