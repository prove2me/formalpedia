-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_ker_coneMapQ_958512f3981d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:49:14.946195+00:00
-- url     : https://prove2.me/submissions/1cab0be9-379a-4fc0-a943-62e2e97fa6ab

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_comap_ker_coneMapQ_41c250fb05d2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_int_eq_zero_327f4c746bd6
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_comap_strictMono
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
    RingHom.ker (coneMapQ y) = ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) := by
  have := hP.2.1.1
  obtain ⟨-, hc, -⟩ := ReciprocityTheory.AnForm.R.extQ_spec (mCoordIdeal y) (int_eq_zero hP)
  have hle : ReciprocityTheory.AnForm.R.extQ (mCoordIdeal y) ≤ RingHom.ker (coneMapQ y) :=
    Ideal.map_le_iff_le_comap.mpr (comap_ker_coneMapQ y).ge
  refine (eq_of_le_of_not_lt hle fun hlt ↦ ?_).symm
  have h := ReciprocityTheory.AnForm.R.IntegerToRational.comap_strictMono hlt
  simp only [hc, comap_ker_coneMapQ] at h
  exact lt_irrefl _ h
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
