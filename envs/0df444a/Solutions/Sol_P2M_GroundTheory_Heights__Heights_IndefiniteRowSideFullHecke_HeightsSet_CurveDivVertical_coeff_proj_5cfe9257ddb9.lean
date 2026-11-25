-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_coeff_proj_5cfe9257ddb9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:07:48.208854+00:00
-- url     : https://prove2.me/submissions/143e8894-af46-41fa-a715-07e7e152215f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Imports
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCurveDivVertical
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_proj_apply_0a7cf4c3995d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CurveDivVertical_weight_eq_zero_iff_afaa2fb5ee83

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
attribute [local instance] MvPolynomial.weightedGradedAlgebra
open Classical
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
theorem _root_.solution (T : Finset K) (f : MRing ι) (d : (Σ k, ι k) →₀ ℕ) :
    coeff d (proj T f) = if ∀ p, d p ≠ 0 → p.1 ∉ T then coeff d f else 0 := by
  classical
  rw [proj_apply, coeff_weightedHomogeneousComponent]
  have : Finsupp.weight (wt T) d = 0 ↔ ∀ p, d p ≠ 0 → p.1 ∉ T := by
    rw [weight_eq_zero_iff]
    refine forall_congr' fun p ↦ imp_congr_right fun _ ↦ ?_
    unfold wt
    split_ifs with h <;> simp [h]
  by_cases h : ∀ p, d p ≠ 0 → p.1 ∉ T
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (mt this.mp h), if_neg h]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CurveDivVertical
