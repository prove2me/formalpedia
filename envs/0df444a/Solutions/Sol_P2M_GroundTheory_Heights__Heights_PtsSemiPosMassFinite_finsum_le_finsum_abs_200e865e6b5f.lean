-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PtsSemiPosMassFinite_finsum_le_finsum_abs_200e865e6b5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:11:46.017862+00:00
-- url     : https://prove2.me/submissions/ed103dec-9b65-40e0-b4ea-200677a2df7f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSemiPosMassFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsSegreChartFibreSum
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StSegreChartAbsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreChartProjFinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PSegreCoordGoodProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSheetHessPSD
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsSemiPosMassFinite
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_M_ima_apply
import Theorems.Thm_ReciprocityTheory_AnForm_M_rea_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
attribute [local simp] ReciprocityTheory.AnForm.M.ima_apply
attribute [local simp] ReciprocityTheory.AnForm.M.rea_apply



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MeasureTheory
open scoped ComplexOrder
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm IsArithVar IsGoodProj pot sheetDensity fibre mcPts segre
  maDensity cxHessian IsSheet)
open GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite
namespace GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite
theorem _root_.solution {α : Type*} (G : α → ℝ) : ∑ᶠ x, G x ≤ ∑ᶠ x, |G x| := by
  have hs : (Function.support fun x => |G x|) = Function.support G := by
    ext x
    simp
  by_cases h : (Function.support G).Finite
  · rw [finsum_eq_sum_of_support_subset G (s := h.toFinset) (by simp),
      finsum_eq_sum_of_support_subset (fun x => |G x|) (s := h.toFinset) (by simp [hs])]
    exact Finset.sum_le_sum fun x _ => le_abs_self _
  · rw [finsum_of_infinite_support h, finsum_of_infinite_support (by rwa [hs])]
end GroundTheory.Heights₂.Heights.PtsSemiPosMassFinite
