-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Chart.dAway_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:51:03.028332+00:00
-- url     : https://prove2.me/submissions/1a980b9f-44b0-4d79-913a-351d9dc533fc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TanSRestrict
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DualMapSOfIdToRingHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Chart_dAway_eps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


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
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Chart
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Type} [CommRing S] (s : S)
namespace ReciprocityTheory.ChartRestriction.G.Chart
theorem _root_.solution {T : Type} [CommRing T] {χ₁ χ₂ : DualNumber (Localization.Away s) →+* T}
    (h : χ₁.comp (dAway s) = χ₂.comp (dAway s)) : χ₁ = χ₂ := by
  have hinl : χ₁.comp (TrivSqZeroExt.inlHom _ _) = χ₂.comp (TrivSqZeroExt.inlHom _ _) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    refine RingHom.ext fun a => ?_
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inl a)
    simp only [RingHom.comp_apply, dAway_inl] at h1
    simpa using h1
  have heps : χ₁ (TrivSqZeroExt.inr 1) = χ₂ (TrivSqZeroExt.inr 1) := by
    have h1 := RingHom.congr_fun h (TrivSqZeroExt.inr 1)
    simp only [RingHom.comp_apply, dAway_eps] at h1
    exact h1
  refine RingHom.ext fun x => ?_
  have h1 := RingHom.congr_fun hinl x.fst
  have h2 := RingHom.congr_fun hinl x.snd
  simp only [RingHom.comp_apply, TrivSqZeroExt.inlHom_apply] at h1 h2
  rw [eq_inl_add_inr x, map_add, map_add, map_mul, map_mul, heps, h1, h2]
end ReciprocityTheory.ChartRestriction.G.Chart
