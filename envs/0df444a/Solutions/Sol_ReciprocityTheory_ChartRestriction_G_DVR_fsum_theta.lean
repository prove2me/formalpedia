-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.fsum_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:14.334307+00:00
-- url     : https://prove2.me/submissions/b3760383-7e9c-4e7b-bce2-fc6da2eba3d1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_single
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
namespace ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
private lemma fsum_eq_sum_single {X Y : Scheme} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    fsum φ ε = ∑ k, Finsupp.single (φ k) (ε k) := rfl
variable {M : LB A.left}
variable {O : Type} [CommRing O] [StarRing O]
end ReciprocityTheory.ChartRestriction.G.DVR
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (x y z : T ⟶ A) :
    fsum (fun I : ULift.{0} (Finset (Fin 3)) => (psum A ![x, y, z] I.down).left)
        (fun I => (-1 : ℤ) ^ (3 - I.down.card)) =
      lf (lamP x (y * z) - lamP x y - lamP x z) := by
  have hu : (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} := by
    decide
  have p0 : psum A ![x, y, z] ∅ = 1 := rfl
  have p1 : psum A ![x, y, z] {0} = x := by
    rw [show psum A ![x, y, z] {0} = x * 1 from rfl, _root_.mul_one]
  have p2 : psum A ![x, y, z] {1} = y := by
    rw [show psum A ![x, y, z] {1} = y * 1 from rfl, _root_.mul_one]
  have p3 : psum A ![x, y, z] {2} = z := by
    rw [show psum A ![x, y, z] {2} = z * 1 from rfl, _root_.mul_one]
  have p01 : psum A ![x, y, z] {0, 1} = x * y := by
    rw [show psum A ![x, y, z] {0, 1} = x * (y * 1) from rfl, _root_.mul_one]
  have p02 : psum A ![x, y, z] {0, 2} = x * z := by
    rw [show psum A ![x, y, z] {0, 2} = x * (z * 1) from rfl, _root_.mul_one]
  have p12 : psum A ![x, y, z] {1, 2} = y * z := by
    rw [show psum A ![x, y, z] {1, 2} = y * (z * 1) from rfl, _root_.mul_one]
  have p012 : psum A ![x, y, z] {0, 1, 2} = x * (y * z) := by
    rw [show psum A ![x, y, z] {0, 1, 2} = x * (y * (z * 1)) from rfl, _root_.mul_one]
  rw [fsum_eq_sum_single, ← Equiv.sum_comp Equiv.ulift.symm]
  simp only [Equiv.ulift_symm_down]
  rw [hu]
  simp (config := {decide := true}) only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton,
    Finset.sum_singleton, not_false_eq_true, or_self, p0, p1, p2, p3, p01, p02, p12, p012]
  simp (config := {decide := true}) only [Finset.card_empty, Finset.card_singleton, Finset.card_insert_of_notMem,
    Finset.mem_insert, Finset.mem_singleton, not_false_eq_true, or_self]
  unfold lamP
  simp only [lf_add, lf_sub, lf_single]
  norm_num
  abel
end ReciprocityTheory.ChartRestriction.G.DVR
