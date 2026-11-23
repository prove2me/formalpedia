-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.TWO.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:10.863363+00:00
-- url     : https://prove2.me/submissions/21f142fe-e6bf-4f08-840d-7d0a018c8228

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ValuationMultiplicationInvariance
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_LBLocalC
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_TWO_fO_comp

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
    [IsProper p] (x : Spec (CommRingCat.of F) ⟶ X) (hx : x ≫ p = Spec.map (CommRingCat.ofHom algVF)) :
    ∃ x' : Spec (CommRingCat.of (Ov v)) ⟶ X, x' ≫ p = Spec.map (CommRingCat.ofHom (fO v hϖ hv)) ∧
      Spec.map (CommRingCat.ofHom (algebraMap (Ov v) F)) ≫ x' = x := by
  have hE : ValuativeCriterion.Existence p := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let S : ValuativeCommSq p :=
    { R := Ov v, K := F, i₁ := x, i₂ := Spec.map (CommRingCat.ofHom (fO v hϖ hv)),
      commSq := ⟨by rw [hx, ← Spec.map_comp, ← CommRingCat.ofHom_comp, fO_comp]⟩ }
  obtain ⟨l⟩ := (hE S).exists_lift
  exact ⟨l.l, l.fac_right, l.fac_left⟩
end ReciprocityTheory.ChartRestriction.G.DVR.TWO
