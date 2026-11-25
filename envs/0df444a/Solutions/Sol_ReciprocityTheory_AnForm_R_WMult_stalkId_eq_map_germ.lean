-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.WMult.stalkId_eq_map_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:34.808426+00:00
-- url     : https://prove2.me/submissions/80854c3d-294d-470f-97c0-9ebbeab150aa

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_WMultA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.WMult
open AlgebraicGeometry CategoryTheory IsLocalRing
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.WMult
theorem _root_.solution (I : W.IdealSheafData) (y : W) (U : W.affineOpens) (hy : y ∈ U.1) :
    FinalTheorems.stalkId I y = Ideal.map (W.presheaf.germ U.1 y hy).hom (I.ideal U) := by
  have key : ∀ (V V' : W.affineOpens) (h : V' ≤ V) (hyV' : y ∈ V'.1),
      Ideal.map (W.presheaf.germ V.1 y ((show V'.1 ≤ V.1 from h) hyV')).hom (I.ideal V) =
        Ideal.map (W.presheaf.germ V'.1 y hyV').hom (I.ideal V') := by
    intro V V' h hyV'
    rw [← I.map_ideal h, Ideal.map_map]
    congr 1
    rw [← CommRingCat.hom_comp]
    exact congrArg CommRingCat.Hom.hom (W.presheaf.germ_res (homOfLE (show V'.1 ≤ V.1 from h)) y hyV').symm
  rw [FinalTheorems.stalkId]
  apply le_antisymm
  · refine iSup₂_le fun V hyV => ?_
    obtain ⟨f, g, hfg, hyf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 y ⟨hy, hyV⟩
    have hWU : W.affineBasicOpen f ≤ U := W.basicOpen_le f
    have hWV : W.affineBasicOpen f ≤ V := by
      show W.basicOpen f ≤ V.1
      rw [hfg]
      exact W.basicOpen_le g
    rw [key V _ hWV hyf, key U _ hWU hyf]
  · exact le_iSup₂ (f := fun (V : W.affineOpens) (hV : y ∈ V.1) =>
      Ideal.map (W.presheaf.germ V.1 y hV).hom (I.ideal V)) U hy
end ReciprocityTheory.AnForm.R.WMult
