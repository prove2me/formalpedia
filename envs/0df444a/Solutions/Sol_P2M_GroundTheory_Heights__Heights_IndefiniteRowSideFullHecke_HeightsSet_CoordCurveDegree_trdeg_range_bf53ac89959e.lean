-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_trdeg_range_bf53ac89959e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:12:02.079138+00:00
-- url     : https://prove2.me/submissions/b5428447-cdaa-4902-8fc6-3da132da2312

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_int_eq_zero_327f4c746bd6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ker_coneMapQ_958512f3981d
import Theorems.Thm_GroundTheory_Arith_Abelian_Jacobian_ringKrullDim_eq_trdeg
import Theorems.Thm_ReciprocityTheory_AnForm_R_extQ_spec


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
    (trdeg ℚ (coneMapQ y).range).toENat = Fintype.card K := by
  have := hP.2.1.1
  obtain ⟨-, -, h⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) (int_eq_zero hP)
  have hd := hP.2.2.2
  have : Algebra.FiniteType ℚ (coneMapQ y).range :=
    Algebra.FiniteType.of_surjective (coneMapQ y).rangeRestrict (coneMapQ y).rangeRestrict_surjective
  rw [← h, ← ker_coneMapQ hP,
    ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange (coneMapQ y)).toRingEquiv,
    GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_trdeg ℚ] at hd
  have h2 : (trdeg ℚ (coneMapQ y).range).toENat + 1 = (Fintype.card K : ℕ∞) + 1 := by
    have e : (((1 + Fintype.card K : ℕ)) : WithBot ℕ∞) = (((Fintype.card K : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) := by
      push_cast; ring
    rw [e] at hd
    exact_mod_cast hd
  exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top) h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
