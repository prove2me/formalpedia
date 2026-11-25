-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.map_germ_ideal_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:08:29.054801+00:00
-- url     : https://prove2.me/submissions/e20ebd8e-4b6d-4c03-8190-fe3206a67a18

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheafA

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
theorem _root_.solution {W : Scheme.{u}} (G : W.IdealSheafData) {U V : W.affineOpens} (h : U ≤ V)
    (x : W) (hx : x ∈ U.1) :
    Ideal.map (W.presheaf.germ V.1 x (h hx)).hom (G.ideal V) =
      Ideal.map (W.presheaf.germ U.1 x hx).hom (G.ideal U) := by
  rw [← G.map_ideal h, Ideal.map_map, ← CommRingCat.hom_comp]
  first
  | (congr 2; exact (TopCat.Presheaf.germ_res W.presheaf _ x hx).symm)
  | (erw [TopCat.Presheaf.germ_res])
  | simp [TopCat.Presheaf.germ_res]
end ReciprocityTheory.AnForm.R
