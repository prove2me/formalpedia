-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_powBlock_lift_not_mem_9ee24b4d2854
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:56:42.546907+00:00
-- url     : https://prove2.me/submissions/62a2e0da-de53-422b-ae20-8723541b19f1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
open MvPolynomial
open scoped ContDiff
open ReciprocityTheory.ChartRestriction.G.Geo (chartRingZ mCoordIdeal chartLat chartLatNm secM mcPts IsArithVar)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open AddBlockData
variable (n)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (k₀ : ι) (e : ℕ) (c : (k : ι) → Fin (n k + 1))
    (j : Fin (n k₀ + 1)) :
    (powBlock n k₀ e).lift ((powChartForms n k₀ e).g c j) ∉ (powBlock n k₀ e).ext := by
  intro h
  unfold AddBlockData.ext ReciprocityTheory.ChartRestriction.G.Geo.mCoordIdeal at h
  rw [RingHom.mem_ker] at h
  simp only [AddBlockData.lift, ReciprocityTheory.ChartRestriction.G.Geo.mConeMap, aeval_rename, powChartForms,
    chartMonomial, map_mul, map_prod, map_pow, aeval_X, Function.comp_apply] at h
  simp only [mul_eq_zero, Finset.prod_eq_zero_iff, pow_eq_zero_iff', C_eq_zero, X_ne_zero,
    or_false] at h
  rcases h with ⟨k, -, h, -⟩ | ⟨h, -⟩
  · exact genPt_whole_ne_zero n _ h
  · exact genPt_whole_ne_zero n _ h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
