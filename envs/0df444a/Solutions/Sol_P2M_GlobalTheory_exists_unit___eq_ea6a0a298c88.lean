-- Prove2me | solution 1 for P2M_GlobalTheory_exists_unit___eq_ea6a0a298c88
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:26.178223+00:00
-- url     : https://prove2.me/submissions/99bfb2a7-3c02-489a-a781-6a3a8cf8f946

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_P2M_GlobalTheory_exists_appLE___eq_fe080a4f4ee7
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_val


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
include hc
namespace GlobalTheory
theorem _root_.solution {i : I} {U : (D.obj i).Opens} (hU : IsAffineOpen U)
    (s : Γ(X, π i ⁻¹ᵁ U)ˣ) :
    ∃ (j : I) (f : j ⟶ i) (t : Γ(D.obj j, D.map f ⁻¹ᵁ U)ˣ), ∀ y : X, y ∈ π i ⁻¹ᵁ U →
      gm (π j) y (D.map f ⁻¹ᵁ U) t = gm (𝟙 X) y (π i ⁻¹ᵁ U) s := by
  obtain ⟨j, f, t, ht⟩ := exists_appLE_π_eq D π w hc hU s.val
  have h₁ : π j ⁻¹ᵁ (D.map f ⁻¹ᵁ U) ≤ π j ⁻¹ᵁ (D.obj j).basicOpen t := by
    have h := X.basicOpen_of_isUnit (ht ▸ s.isUnit)
    rw [Scheme.basicOpen_appLE] at h
    rw [← Scheme.Hom.comp_preimage, w, ← h]
    exact inf_le_right
  obtain ⟨k, g, hg⟩ := exists_map_preimage_le_map_preimage D _ hc (hU.preimage (D.map f)).isCompact h₁
  have le : D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have hu : IsUnit (((D.map g).appLE _ _ le).hom t) := by
    refine (D.obj k).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ?_
    refine ((D.obj k).mem_basicOpen _ y hy).1 ?_
    rw [Scheme.basicOpen_appLE]
    exact ⟨hy, hg (le hy)⟩
  refine ⟨k, g ≫ f, hu.unit, fun y hy => Units.ext ?_⟩
  have hy' := cone_preimage_le D π w (g ≫ f) U hy
  rw [gm_val _ y _ hy', gm_val (𝟙 X) y _ hy, IsUnit.unit_spec, ← ht]
  have e : (D.map g).appLE _ _ le ≫ (π k).appLE _ _ (cone_preimage_le D π w (g ≫ f) U) =
      (π j).appLE _ _ (cone_preimage_le D π w f U) := by
    simp only [Scheme.Hom.appLE_comp_appLE, w]
  rw [← e]
  exact (TopCat.Presheaf.germ_res_apply X.presheaf
    (homOfLE (cone_preimage_le D π w (g ≫ f) U)) y hy _).symm
end GlobalTheory
