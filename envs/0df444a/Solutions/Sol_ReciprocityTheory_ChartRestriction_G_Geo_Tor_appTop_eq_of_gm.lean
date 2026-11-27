-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.appTop_eq_of_gm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:25:30.917524+00:00
-- url     : https://prove2.me/submissions/b6bcec20-274f-411d-810b-f3c397084dbb

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsTor
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_FnOfComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_GtPtsVal

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {Y Z W : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (τ₁ τ₂ : Z ⟶ Y) (c₁ c₂ : Γ(Y, ⊤)ˣ) (h : ∀ z, gm τ₁ z ⊤ c₁ = gm τ₂ z ⊤ c₂) :
    τ₁.appTop.hom c₁.val = τ₂.appTop.hom c₂.val := by
  apply TopCat.Presheaf.section_ext Z.sheaf ⊤
  intro z hz
  have h1 := congrArg Units.val (h z)
  unfold gm pullU at h1
  have m1 : τ₁ z ∈ (⊤ : Y.Opens) := trivial
  have m2 : τ₂ z ∈ (⊤ : Y.Opens) := trivial
  rw [dif_pos m1, dif_pos m2] at h1
  simp only [MonoidHom.comp_apply, Units.coe_map, MonoidHom.coe_coe] at h1
  exact h1
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
