-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWO.lift_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:32.982287+00:00
-- url     : https://prove2.me/submissions/88a82246-aeb7-4ec8-8caa-53a8901da722

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.TWO
open ReciprocityTheory.ChartRestriction.G.Out
variable {F : Type} [Field F] (v : AddValuation F (WithTop ℚ))
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
  [Algebra (FractionRing V) F]
namespace ReciprocityTheory.ChartRestriction.G.DVR.TWO
theorem _root_.solution (hϖ : Irreducible ϖ) (hv : ValOver ϖ F v) {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of V))
    [IsSeparated p] (x₁ x₂ : Spec (CommRingCat.of (Ov v)) ⟶ X)
    (h₁ : x₁ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv))) (h₂ : x₂ ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)))
    (h : Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁ = Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₂) :
    x₁ = x₂ := by
  let S : ValuativeCommSq p :=
    { R := Ov v, K := F, i₁ := Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x₁,
      i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)),
      commSq := ⟨by rw [Category.assoc, h₁]⟩ }
  have hU : Subsingleton S.commSq.LiftStruct := IsSeparated.valuativeCriterion p S
  have hl : (⟨x₁, rfl, h₁⟩ : S.commSq.LiftStruct) = ⟨x₂, h.symm, h₂⟩ := @Subsingleton.elim _ hU _ _
  exact congrArg CommSq.LiftStruct.l hl
end ReciprocityTheory.ChartRestriction.G.DVR.TWO
