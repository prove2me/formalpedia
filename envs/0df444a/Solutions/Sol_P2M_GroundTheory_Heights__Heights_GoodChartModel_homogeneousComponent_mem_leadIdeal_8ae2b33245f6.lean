-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GoodChartModel_homogeneousComponent_mem_leadIdeal_8ae2b33245f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:14:28.187514+00:00
-- url     : https://prove2.me/submissions/88f75596-6c43-4bf3-ae77-87af170c7665

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartModel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartZeroSet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StGoodChartDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjHomInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeAvoidsFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PGoodChartModel
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_segre_rel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix
open GroundTheory.Heights₂.Heights.GoodChartModel
namespace GroundTheory.Heights₂.Heights.GoodChartModel
theorem _root_.solution {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _
end GroundTheory.Heights₂.Heights.GoodChartModel
