-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exSection_supNormLE_140b548c5a2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:56:32.360404+00:00
-- url     : https://prove2.me/submissions/bceaeb57-98de-4bf2-9437-b3a3e12c6c74

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution :
    IntegralSection.SupNormLE (powDivStd (HermLine.standard projectiveLineSizes) 1) exSection 0 := by
  intro z hz c d e' he _
  obtain ⟨-, hmem⟩ := he
  have h0 : e' = chartMonomial c d := by
    have := (Submodule.mem_bot _).mp hmem
    simpa [exSection, constSection, sub_eq_zero] using this
  subst h0
  have hS := ((HermLine.standard projectiveLineSizes).metric_pos z hz.1).ne'
  have hm : (powDivStd (HermLine.standard projectiveLineSizes) 1).metric z = 1 := by
    change (HermLine.standard projectiveLineSizes).metric z ^ 1 / (HermLine.standard projectiveLineSizes).metric z = 1
    rw [pow_one, div_self hS]
  rw [hm, mul_one, Real.exp_zero]
  exact div_self_le_one _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
