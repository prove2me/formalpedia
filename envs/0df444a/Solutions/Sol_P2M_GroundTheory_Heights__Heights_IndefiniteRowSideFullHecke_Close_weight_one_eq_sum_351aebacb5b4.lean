-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_one_eq_sum_351aebacb5b4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:07.158454+00:00
-- url     : https://prove2.me/submissions/462ff464-ddd8-46e5-a967-e70ebc01969a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_SectionInjectivityHypothesesProjectiveLine
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_OneBlockIdealEqComapProjIdeal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_RenameBlockIsWeightedHomogeneous
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Close_weight_coordDeg_apply_ad5acafbd2e4

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
open ReciprocityTheory.ChartRestriction.G.Geo (secM sec IsMultiHomog)
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
theorem _root_.solution (d : Coord n →₀ ℕ) :
    Finsupp.weight 1 d = ∑ k, Finsupp.weight (coordDeg n) d k := by
  simp_rw [weight_coordDeg_apply]
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), ← Fintype.sum_sigma]
  simp
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Close
