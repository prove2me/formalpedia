-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:29:52.620959+00:00
-- url     : https://prove2.me/submissions/7baafdae-73b4-4a7c-8af8-722fdf2eaaf4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_mul_left_congr


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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
variable {S S' : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution {G₁ G₂ : Over S} [GrpObj G₁] [GrpObj G₂] (e : G₁ ≅ G₂) [IsMonHom e.hom] :
    IsGrpPullback G₁ G₂ (𝟙 S) e.hom.left := by
  have : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  refine ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  rw [← Over.comp_left, MonObj.mul_comp]
  obtain ⟨Tl, ⟨⟨⟩⟩, Th⟩ := T
  exact mul_left_congr (Category.comp_id _) x₀ y₀ (x ≫ e.hom) (y ≫ e.hom) hx hy
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
