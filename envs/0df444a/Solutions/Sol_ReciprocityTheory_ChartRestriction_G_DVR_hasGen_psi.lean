-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.hasGen_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:08:30.110909+00:00
-- url     : https://prove2.me/submissions/8bde6084-ace9-4bc7-9478-d23a35a18f0a

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_single
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_padd_eq_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_single_two
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
theorem _root_.solution (w : A ⟶ A)
    (u : LB.Gen (LB.LinComb M (K := Fin 4)
      ![(padd A (𝟙 _) w).left, 𝟙 A.left, w.left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]))
    (hu : u.IsGen) (y : T ⟶ A) : HasGen M (lf (psiP w y)) := by
  have h0 := HasGen.of_gen (L := M) u hu
  have h1 := h0.pull y.left
  rw [mapDomain_comp_fsum] at h1
  convert h1 using 1
  have e1 : y.left ≫ (padd A (𝟙 _) w).left = (y * (y ≫ w)).left := by
    rw [← Over.comp_left, padd_eq_mul, MonObj.comp_mul, Category.comp_id]
  have e2 : y.left ≫ (𝟙 A : A ⟶ A).left = y.left := by
    rw [← Over.comp_left, Category.comp_id]
  have e3 : y.left ≫ w.left = (y ≫ w).left := by
    rw [← Over.comp_left]
  have e4 : y.left ≫ (toUnit A ≫ η[A]).left = (1 : T ⟶ A).left := by
    rw [← Over.comp_left, ← Category.assoc, CartesianMonoidalCategory.comp_toUnit]
    rfl
  rw [fsum_eq_sum_single]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero]
  rw [e1, Category.comp_id, e3, e4]
  unfold psiP lamP
  simp only [lf_add, lf_sub, lf_single, Finsupp.single_neg, single_two]
  abel
end ReciprocityTheory.ChartRestriction.G.DVR
