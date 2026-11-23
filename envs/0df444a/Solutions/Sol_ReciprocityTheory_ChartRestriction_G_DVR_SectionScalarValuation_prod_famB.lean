-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.prod_famB
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:14:17.736212+00:00
-- url     : https://prove2.me/submissions/cb581465-34a9-4cdb-973a-b6d438a0e01c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ProdNeg

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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)
namespace ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
theorem _root_.solution {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (χ : D.X) (k : ℕ) {U : Type} [CommGroup U]
    (h : (T.left ⟶ D.P.A.left) → U) : ∏ i, h (ρ.left ≫ D.famφB χ i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (ρ * cQ D T χ).left * (h (cQ D T χ).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e1 : ρ.left ≫ (𝟙 D.P.A.left) = ρ.left := Category.comp_id _
  have e2 : ρ.left ≫ (padd D.P.A (𝟙 D.P.A) (toUnit _ ≫ D.c χ)).left = (ρ * cQ D T χ).left := by
    rw [← Over.comp_left]
    congr 1
    rw [padd, Hom.mul_def, comp_lift_assoc, Category.comp_id, cQ, ← Category.assoc, comp_toUnit]
  have e3 : ρ.left ≫ (toUnit D.P.A ≫ D.c χ).left = (cQ D T χ).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
    rfl
  have e4 : ρ.left ≫ (toUnit D.P.A ≫ η[D.P.A]).left = (1 : T ⟶ D.P.A).left := by
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit, Hom.one_def]
  rw [Fin.prod_univ_four]
  simp only [DegPre.famφB, DegPre.famε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, zpow_one, zpow_neg, e1, e2, e3, e4]
end ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation
