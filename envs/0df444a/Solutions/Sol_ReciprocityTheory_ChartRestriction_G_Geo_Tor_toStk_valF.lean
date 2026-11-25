-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.Tor.toStk_valF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:11:28.062765+00:00
-- url     : https://prove2.me/submissions/6c9dc4b6-8019-4be4-bbb8-386b0dc7ca77

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_OLinBaseChangeSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_top_le_iff_mem

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
variable {F : Type} [Field F] {X : Scheme.{0}}
namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor
theorem _root_.solution (x : Sp F ⟶ X) (U : X.Opens) (z : Sp F) (h : x z ∈ U) (a : Γ(X, U)ˣ) :
    toStk z (valF x U a.val) = (gm x z U a).val := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := (top_le_iff_mem x U z).2 h
  have e1 := congrArg (fun g => g.hom ((x.appLE U ⊤ h').hom a.val))
    (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at e1
  rw [valF, dif_pos h', gm, dif_pos h]
  simp only [toStk, RingHom.comp_apply, MonoidHom.comp_apply, Units.coe_map, pullU,
    RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  rw [e1]
  first
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       exact TopCat.Presheaf.germ_res_apply _ _ _ _ _)
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       erw [TopCat.Presheaf.germ_res_apply])
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       exact (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans rfl)
    | (simp only [Scheme.Hom.appLE, CommRingCat.hom_comp, RingHom.comp_apply]
       exact Eq.refl _)
end ReciprocityTheory.ChartRestriction.G.Geo.Tor
