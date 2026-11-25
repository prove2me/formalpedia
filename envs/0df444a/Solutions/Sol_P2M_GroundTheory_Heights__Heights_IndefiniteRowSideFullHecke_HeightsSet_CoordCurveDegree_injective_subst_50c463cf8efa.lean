-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_HeightsSet_CoordCurveDegree_injective_subst_50c463cf8efa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:12:22.530888+00:00
-- url     : https://prove2.me/submissions/3f003a5f-5645-4a5e-9f68-b3e5cc76eccf

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_CoordCurveDegree
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_PCoordCurveAlgebraic

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
theorem _root_.solution (k₀ : K) :
    Function.Injective (aeval (Sum.elim (fun k ↦ X (Sum.inl k)) fun _ : Unit ↦
      X (Sum.inr ()) * X (Sum.inl k₀)) : MvPolynomial (K ⊕ Unit) ℚ →ₐ[ℚ] MvPolynomial (K ⊕ Unit) ℚ) := by
  set L := FractionRing (MvPolynomial (K ⊕ Unit) ℚ)
  let f := algebraMap (MvPolynomial (K ⊕ Unit) ℚ) L
  have h0 : f (X (Sum.inl k₀)) ≠ 0 :=
    (map_ne_zero_iff f (IsFractionRing.injective _ L)).mpr (X_ne_zero _)
  let η : MvPolynomial (K ⊕ Unit) ℚ →ₐ[ℚ] L :=
    aeval (Sum.elim (fun k ↦ f (X (Sum.inl k))) fun _ ↦ f (X (Sum.inr ())) / f (X (Sum.inl k₀)))
  have hη : η.comp (aeval (Sum.elim (fun k ↦ X (Sum.inl k)) fun _ : Unit ↦
      X (Sum.inr ()) * X (Sum.inl k₀))) = IsScalarTower.toAlgHom ℚ _ L := by
    refine MvPolynomial.algHom_ext fun i ↦ ?_
    rcases i with k | u
    · simp [η, f]
    · simp only [AlgHom.comp_apply, aeval_X, Sum.elim_inr, map_mul, η, Sum.elim_inl,
        IsScalarTower.coe_toAlgHom']
      rw [div_mul_cancel₀ _ h0]
  intro a b hab
  apply IsFractionRing.injective (MvPolynomial (K ⊕ Unit) ℚ) L
  have := congrArg η hab
  rw [← AlgHom.comp_apply, ← AlgHom.comp_apply, hη] at this
  exact this
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet.CoordCurveDegree
