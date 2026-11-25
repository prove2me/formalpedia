-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_isAlgebraic_blockFnField_1c5e3fe2724f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:56:21.11371+00:00
-- url     : https://prove2.me/submissions/ac41a9c7-925a-4725-801e-6dfb82e7491d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_X_mem_of_eq_zero_e9e44dbdbf54
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_isAlgebraic_ratio_a456e2cba585

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 Algebra
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
set_option linter.unusedSectionVars false
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
theorem _root_.solution {y : (Σ k, ι k) → Ω} (hP : IsArithVar (mCoordIdeal y) 1) :
    Algebra.IsAlgebraic ℚ (blockFnField y) := by
  classical
  choose c hc using hP.2.1.2.2
  have hc' : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h ↦ hc k (X_mem_of_eq_zero h)
  refine IntermediateField.isAlgebraic_adjoin fun t ⟨p, q, hpq, ht⟩ ↦ ?_
  subst ht
  by_cases hq : y q = 0
  · rw [hq, div_zero]
    exact isIntegral_zero
  have hd : ∀ k', y ⟨k', Function.update c q.1 q.2 k'⟩ ≠ 0 := by
    intro k'
    by_cases h : k' = q.1
    · subst h; simpa using hq
    · simpa [Function.update_of_ne h] using hc' k'
  have e : (⟨p.1, Function.update c q.1 q.2 p.1⟩ : Σ k, ι k) = q := by
    obtain ⟨k, i⟩ := p
    obtain ⟨k', j⟩ := q
    simp only at hpq
    subst hpq
    simp
  have := isAlgebraic_ratio hP (Function.update c q.1 q.2) hd p
  rw [e] at this
  exact this.isIntegral
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
