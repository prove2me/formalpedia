-- Prove2me | solution 1 for P2M_GlobalTheory_exists_appLE___eq_fe080a4f4ee7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:08:58.287523+00:00
-- url     : https://prove2.me/submissions/fe7bfffe-d2dc-495a-8bae-39ff8ef70a99

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {I : Type} [SmallCategory I] [IsCofiltered I]
variable (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]
set_option backward.isDefEq.respectTransparency false
include hc
namespace GlobalTheory
theorem _root_.solution {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U)
    (s : Γ(X, π i ⁻¹ᵁ U)) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)),
      ((π j).appLE _ _ (cone_preimage_le D π w f U)).hom t = s := by
  have (j : Over i) : IsAffine ((opensDiagram D i U).obj j) := hU.preimage (D.map _)
  obtain ⟨j, t, hj⟩ := exists_appTop_π_eq_of_isAffine_of_isLimit _ _
    (isLimitOpensCone D _ hc i U) ((π i ⁻¹ᵁ U).topIso.inv s)
  refine ⟨j.left, j.hom, (D.map j.hom ⁻¹ᵁ U).topIso.hom t, ?_⟩
  have h := (congrArg (π i ⁻¹ᵁ U).topIso.hom hj).trans (Iso.inv_hom_id_apply _ s)
  have e : ∀ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U)
      (t : Γ(U.toScheme, ⊤)), (f.appLE U V e).hom (U.topIso.hom t) =
        V.topIso.hom ((f.resLE U V e).appTop t) := by
    intro X Y f U V e t
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply, CommRingCat.comp_apply,
      Iso.inv_hom_id_apply]
  exact (e _ _ _ _ t).trans h
end GlobalTheory
