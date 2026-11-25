-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointsBilinear_finsum_mem_sum_comm_99abf742b05d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:47:20.129303+00:00
-- url     : https://prove2.me/submissions/e89dec16-9e86-4497-a710-6bb5911a25b8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_MdiscSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_CasChainA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StPtsBilinear
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PtsIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PPtsBilinear

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
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
open GroundTheory.Heights₂.Heights.PointsBilinear
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.PointsBilinear
theorem _root_.solution {α T : Type*} [Fintype T] {S : Set α} (hS : S.Finite) (F : T → α → ℝ) :
    ∑ᶠ w ∈ S, ∑ t, F t w = ∑ t, ∑ᶠ w ∈ S, F t w := by
  rw [finsum_mem_eq_finite_toFinset_sum _ hS, Finset.sum_comm]
  exact Finset.sum_congr rfl fun t _ => (finsum_mem_eq_finite_toFinset_sum _ hS).symm
end GroundTheory.Heights₂.Heights.PointsBilinear
