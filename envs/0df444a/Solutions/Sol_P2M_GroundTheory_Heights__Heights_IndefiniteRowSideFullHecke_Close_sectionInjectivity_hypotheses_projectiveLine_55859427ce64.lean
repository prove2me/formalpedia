-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_sectionInjectivity_hypotheses_projectiveLine_55859427ce64
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:16.988084+00:00
-- url     : https://prove2.me/submissions/eeb4d7bb-13e1-47fd-9f96-8a1a0a7eeb30

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Points
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Slopes
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_exSection_supNormLE_140b548c5a2a

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
    1 < 2 ∧ 1 ≤ 1 ∧ exSection.num ∉ (ArithVariety.whole projectiveLineSizes).ideal ∧
      IntegralSection.SupNormLE (powDivStd (HermLine.standard projectiveLineSizes) 1) exSection 0 ∧
      (powBlock projectiveLineSizes () 2).deg = (twistPow (HermLine.standard projectiveLineSizes) (2 - 1) 1 0).deg := by
  refine ⟨by norm_num, le_rfl, ?_, exSection_supNormLE, ?_⟩
  · intro h
    have := (Submodule.mem_bot _).mp h
    simp [exSection, constSection] at this
  · funext b
    simp [powBlock, twistPow, HermLine.standard]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
