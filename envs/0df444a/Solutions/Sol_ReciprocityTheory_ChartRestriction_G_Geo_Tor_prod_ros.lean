-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_ros
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:25:16.119471+00:00
-- url     : https://prove2.me/submissions/aa93f922-622d-4507-93e3-70bf94120beb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
variable [IsCommMonObj A] {L : LB A.left}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (f g : A ⟶ A) {T : Over S} (x y : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ i, h ((lift x y).left ≫ rosatiφ A f g i) ^ rosatiε i =
      h ((x ≫ f) * y).left * (h (x ≫ f).left)⁻¹ * (h y.left)⁻¹ * (h (x * (y ≫ g)).left)⁻¹ * h x.left * h (y ≫ g).left := by
  have e : ∀ k : A ⊗ A ⟶ A, (lift x y).left ≫ k.left = (lift x y ≫ k).left := fun k => by
    rw [Over.comp_left]
  have m1 : ∀ a b : A ⊗ A ⟶ A, (lift x y ≫ padd A a b).left = ((lift x y ≫ a) * (lift x y ≫ b)).left := by
    intro a b
    first
      | (simp only [padd, comp_lift_assoc]; rfl)
      | (simp only [padd, ← Category.assoc, comp_lift]; rfl)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, rosatiφ, rosatiε, Matrix.cons_val_zero,
    Matrix.cons_val_succ, e, m1, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, zpow_one, zpow_neg,
    mul_one]
  first
    | ac_rfl
    | (simp only [mul_comm, mul_assoc, mul_left_comm]; done)
    | (rw [← mul_inv_eq_one]; simp only [mul_inv_rev, inv_inv, mul_comm, mul_assoc, mul_left_comm, inv_mul_cancel, mul_inv_cancel]; done)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
