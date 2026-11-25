-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.hasGen_rosati
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:09:19.382089+00:00
-- url     : https://prove2.me/submissions/679756e3-b715-4b01-a374-b48bb02cffa2

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_padd_eq_mul
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
theorem _root_.solution (f g : A ⟶ A)
    (u : LB.Gen (LB.LinComb M (Out.rosatiφ A f g) Out.rosatiε)) (hu : u.IsGen) (x z : T ⟶ A) :
    HasGen M (lf (lamP (x ≫ f) z - lamP x (z ≫ g))) := by
  have h0 := HasGen.of_gen (L := M) u hu
  have h1 := h0.pull (lift x z).left
  rw [mapDomain_comp_fsum] at h1
  convert h1 using 1
  have r0 : (lift x z).left ≫ (padd A (fst A A ≫ f) (snd A A)).left = ((x ≫ f) * z).left := by
    rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, ← Category.assoc, CartesianMonoidalCategory.lift_fst,
      CartesianMonoidalCategory.lift_snd]
  have r1 : (lift x z).left ≫ (fst A A ≫ f).left = (x ≫ f).left := by
    rw [← Over.comp_left, ← Category.assoc, CartesianMonoidalCategory.lift_fst]
  have r2 : (lift x z).left ≫ (snd A A).left = z.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_snd]
  have r3 : (lift x z).left ≫ (padd A (fst A A) (snd A A ≫ g)).left = (x * (z ≫ g)).left := by
    rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, CartesianMonoidalCategory.lift_fst, ← Category.assoc,
      CartesianMonoidalCategory.lift_snd]
  have r4 : (lift x z).left ≫ (fst A A).left = x.left := by
    rw [← Over.comp_left, CartesianMonoidalCategory.lift_fst]
  have r5 : (lift x z).left ≫ (snd A A ≫ g).left = (z ≫ g).left := by
    rw [← Over.comp_left, ← Category.assoc, CartesianMonoidalCategory.lift_snd]
  rw [fsum_eq_sum_single]
  simp only [Out.rosatiφ, Out.rosatiε, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, add_zero]
  rw [r0, r1, r2, r3, r4, r5]
  unfold lamP
  simp only [lf_add, lf_sub, lf_single, Finsupp.single_neg]
  abel
end ReciprocityTheory.ChartRestriction.G.DVR
