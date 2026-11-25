-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.hasGen_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:34.004997+00:00
-- url     : https://prove2.me/submissions/dc1b3136-b344-491a-963c-9b1ca9eb16f0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_psum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_cartesian_lift_three_comp_projection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_fsum_theta
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_of_gen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_pull

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
private lemma mapDomain_comp_fsum {X Y Z : Scheme} {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Z ⟶ Y) :
    Finsupp.mapDomain (fun ψ => h ≫ ψ) (fsum φ ε) = fsum (fun k => h ≫ φ k) ε := by
  rw [fsum_eq_sum_single, fsum_eq_sum_single, Finsupp.mapDomain_finset_sum]
  simp only [Finsupp.mapDomain_single]
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
variable {M : LB A.left}
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (t : LB.Gen (Theta A M)) (ht : t.IsGen) (x y z : T ⟶ A) :
    HasGen M (lf (lamP x (y * z) - lamP x y - lamP x z)) := by
  have h0 := HasGen.of_gen (L := M)
    (φ := fun I : ULift.{0} (Finset (Fin 3)) => (psum A (x3 A) I.down).left)
    (ε := fun I => (-1 : ℤ) ^ (3 - I.down.card)) t ht
  have h1 := h0.pull (lift x (lift y z)).left
  rw [mapDomain_comp_fsum] at h1
  rw [← fsum_theta]
  convert h1 using 2
  funext I
  rw [← Over.comp_left, comp_psum, cartesian_lift_three_comp_projection]
end ReciprocityTheory.ChartRestriction.G.DVR
