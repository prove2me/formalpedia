-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_MongeAmpereComparison_cutoff_of_one_le_7e6202384246
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:40:18.488069+00:00
-- url     : https://prove2.me/submissions/75e5c529-7441-415c-8ee5-5ebe295519f6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_Statements
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffOnFubiniStudyProfileInvNormSqFirst
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffAtOfIsPotential
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PMongeAmpereComparison

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
namespace GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
theorem _root_.solution {t : ℝ} (ht : 1 ≤ t) : cutoff t = t - (1 - cutoff 1) := by
  have hc := Real.smoothTransition.continuous
  have h1 : ∫ u in (1 : ℝ)..t, Real.smoothTransition u = ∫ _ in (1 : ℝ)..t, (1 : ℝ) :=
    intervalIntegral.integral_congr fun u hu => by
      rw [Set.uIcc_of_le ht] at hu
      exact Real.smoothTransition.one_of_one_le hu.1
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable (μ := volume) 0 1)
    (hc.intervalIntegrable (μ := volume) 1 t)
  rw [h1, intervalIntegral.integral_const, smul_eq_mul, mul_one] at h2
  unfold cutoff
  linarith
end GroundTheory.Heights₂.Heights.FourB.MongeAmpereComparison
