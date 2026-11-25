-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TubeFormComparison_norm_sq_le_sum_655fe36f7161
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:22:59.432115+00:00
-- url     : https://prove2.me/submissions/53968c43-ac4c-4e1c-a775-bab0a2f7c993

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCIsHermitian
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeFormCompare

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder
noncomputable section
open GroundTheory.Heights₂.Heights.TubeFormComparison
namespace GroundTheory.Heights₂.Heights.TubeFormComparison
theorem _root_.solution {N : ℕ} (v : Fin N → ℂ) : ‖v‖ ^ 2 ≤ ∑ j, ‖v j‖ ^ 2 := by
  have hS : 0 ≤ ∑ j, ‖v j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h : ‖v‖ ≤ Real.sqrt (∑ j, ‖v j‖ ^ 2) := by
    refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => ?_
    exact (le_abs_self _).trans (Real.abs_le_sqrt (Finset.single_le_sum
      (f := fun j => ‖v j‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ j)))
  calc ‖v‖ ^ 2 ≤ Real.sqrt (∑ j, ‖v j‖ ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := Real.sq_sqrt hS
end GroundTheory.Heights₂.Heights.TubeFormComparison
