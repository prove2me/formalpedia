-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.DVR.hasGen_pullMul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:30:04.869656+00:00
-- url     : https://prove2.me/submissions/db2dee3e-ecd4-4170-b0d1-7b1609af375e

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_HasGen
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_CartesianLiftThreeCompProjection
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_lf_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_lam_pow
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_psi
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_hasGen_rosati
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_DVR_comp_pow__ea2edb35d3f7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_act_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_HasGen_zsmul


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
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.DVR
open ReciprocityTheory.ChartRestriction.G.Semi
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T T' : Over S}
variable {M : LB A.left}
variable {O : Type} [CommRing O] [StarRing O]
namespace ReciprocityTheory.ChartRestriction.G.DVR
theorem _root_.solution (ra : Out.RingAct A O) (w0 a : O) (N : ℕ) (hN : a * star a = (N : O))
    (uΨ : LB.Gen (LB.LinComb M (K := Fin 4)
      ![(padd A (𝟙 _) (ra.act w0)).left, 𝟙 A.left, (ra.act w0).left, (toUnit A ≫ η[A]).left] ![1, -2, -1, 2]))
    (huΨ : uΨ.IsGen)
    (uR : LB.Gen (LB.LinComb M (Out.rosatiφ A (ra.act a) (ra.act (star a))) Out.rosatiε)) (huR : uR.IsGen)
    (t : LB.Gen (Theta A M)) (ht : t.IsGen) :
    HasGen M (lf (Finsupp.single (ra.act a) 1 - (N : ℤ) • Finsupp.single (𝟙 A) 1 +
      ((N : ℤ) - 1) • Finsupp.single (1 : A ⟶ A) 1)) := by
  have hΨa := hasGen_psi (ra.act w0) uΨ huΨ (ra.act a)
  have hΨ1 := hasGen_psi (ra.act w0) uΨ huΨ (𝟙 A)
  have hR := hasGen_rosati (ra.act a) (ra.act (star a)) uR huR (𝟙 A) (ra.act a ≫ ra.act w0)
  have hP := hasGen_lam_pow t ht (𝟙 A) (ra.act w0) N
  have hz : (ra.act a ≫ ra.act w0) ≫ ra.act (star a) = (ra.act w0) ^ N := by
    rw [← ra.map_mul, ← ra.map_mul]
    have h1 : star a * (w0 * a) = (N : O) * w0 := by
      rw [← hN]
      ring
    rw [h1, ra.map_mul, act_natCast, comp_pow', Category.comp_id]
  have key : Finsupp.single (ra.act a) 1 - (N : ℤ) • Finsupp.single (𝟙 A) 1 +
      ((N : ℤ) - 1) • Finsupp.single (1 : A ⟶ A) 1 =
      -(psiP (ra.act w0) (ra.act a)) +
        (lamP (𝟙 A ≫ ra.act a) (ra.act a ≫ ra.act w0) - lamP (𝟙 A) ((ra.act a ≫ ra.act w0) ≫ ra.act (star a))) +
        (lamP (𝟙 A) (ra.act w0 ^ N) - (N : ℤ) • lamP (𝟙 A) (ra.act w0)) +
        (N : ℤ) • psiP (ra.act w0) (𝟙 A) := by
    rw [hz, Category.id_comp]
    unfold psiP
    rw [Category.id_comp]
    module
  rw [key, lf_add, lf_add, lf_add, lf_neg, lf_smul]
  exact (((hΨa.neg).add hR).add hP).add (hΨ1.zsmul _)
end ReciprocityTheory.ChartRestriction.G.DVR
