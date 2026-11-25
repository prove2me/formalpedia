-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.ds_stalkId_eq_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:14:52.487795+00:00
-- url     : https://prove2.me/submissions/f9e0363d-4c78-451a-ad9b-e98dcaee6921

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA
import Theorems.Thm_ReciprocityTheory_AnForm_R_map_germ_ideal_eq_of_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory
noncomputable section
universe u
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {W : Scheme.{u}} (G : W.IdealSheafData) (U : W.affineOpens) (x : W)
    (hx : x ∈ U.1) :
    FinalTheorems.stalkId G x = Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U) := by
  unfold FinalTheorems.stalkId
  apply le_antisymm
  · refine iSup₂_le fun U' hx' => ?_
    have hxi : x ∈ U.1 ⊓ U'.1 := by
      first
      | exact ⟨hx, hx'⟩
      | exact TopologicalSpace.Opens.mem_inf.mpr ⟨hx, hx'⟩
      | simp [hx, hx']
    obtain ⟨O, hO, hxO, hOle⟩ : ∃ O ∈ W.affineOpens, x ∈ O ∧ O ≤ U.1 ⊓ U'.1 := by
      first
      | (obtain ⟨f, hf1, hf2⟩ := U.2.exists_basicOpen_le (V := U'.1) ⟨x, hx'⟩ hx
         exact ⟨W.basicOpen f, U.2.basicOpen f, hf2, le_inf (W.basicOpen_le f) hf1⟩)
      | exact (TopologicalSpace.Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.isBasis_affine_open W)) hxi
      | exact (TopologicalSpace.Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens) hxi
    let U'' : W.affineOpens := ⟨O, hO⟩
    have h1 : U'' ≤ U := (le_inf_iff.mp hOle).1
    have h2 : U'' ≤ U' := (le_inf_iff.mp hOle).2
    exact ((map_germ_ideal_eq_of_le G h2 x hxO).trans (map_germ_ideal_eq_of_le G h1 x hxO).symm).le
  · exact le_iSup₂ (f := fun (U : W.affineOpens) (hx : x ∈ U.1) =>
      Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U)) U hx
end ReciprocityTheory.AnForm.R
