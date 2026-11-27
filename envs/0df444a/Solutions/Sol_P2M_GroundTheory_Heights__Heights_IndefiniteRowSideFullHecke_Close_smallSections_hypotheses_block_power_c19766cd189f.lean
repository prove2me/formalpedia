-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_smallSections_hypotheses_block_power_c19766cd189f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:56:21.183733+00:00
-- url     : https://prove2.me/submissions/17a01f40-bc8f-461d-b53b-f1c7a26bb273

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
theorem _root_.solution (k₀ : ι) :
    (MvPolynomial.IsHomogeneous (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ) 0) ∧
    (∀ w ∈ conePoints (powBlock n k₀ 1).ext ℂ,
      ‖eval₂ (Int.castRingHom ℂ) (newPart w) (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ)‖ ≤
        hPlus (powChartForms n k₀ 1) (wholeGens n) (blockPowLine n k₀ 1) w ^ 0) ∧
    val (ArithVariety.whole n) 1 =
      aeval (powBlock n k₀ 1).x (1 : MvPolynomial (Fin ((powBlock n k₀ 1).m + 1)) ℤ) *
        val (ArithVariety.whole n) 1 :=
  ⟨isHomogeneous_one _ _, fun w _ ↦ by simp, by simp [val]⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
