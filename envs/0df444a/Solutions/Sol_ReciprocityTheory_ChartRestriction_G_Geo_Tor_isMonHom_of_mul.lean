-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isMonHom_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:18.818496+00:00
-- url     : https://prove2.me/submissions/05c82fc7-37ee-463f-bbdf-7f66e84f0ea7

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigIsoCongr
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsMonHomOfMul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr


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
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {S : Scheme.{0}} {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ⟶ G₂)
    (mul : ∀ (T : Over S) (x y : T ⟶ G₁), (x * y) ≫ e = (x ≫ e) * (y ≫ e)) : IsMonHom e := by
  have hμ : μ ≫ e = (e ⊗ₘ e) ≫ μ := by
    have h := mul _ (fst G₁ G₁) (snd G₁ G₁)
    simp only [Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]
    congr 1
  have h1 : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ e = 1 := by
    have h := mul _ (1 : 𝟙_ (Over S) ⟶ G₁) 1
    rw [_root_.mul_one] at h
    exact mul_left_cancel (a := (1 : 𝟙_ (Over S) ⟶ G₁) ≫ e) (by rw [_root_.mul_one, ← h])
  have hu : toUnit (𝟙_ (Over S)) = 𝟙 _ := toUnit_unique _ _
  simp only [Hom.one_def, hu, Category.id_comp] at h1
  exact ⟨h1, hμ⟩
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
