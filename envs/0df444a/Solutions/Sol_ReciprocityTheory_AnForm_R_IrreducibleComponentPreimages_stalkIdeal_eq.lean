-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.stalkIdeal_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:50:04.237286+00:00
-- url     : https://prove2.me/submissions/63b02294-ff49-4bb4-a846-85af250de332

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ClosureFromSpecMemCompsH
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace
noncomputable section
variable {W : Scheme.{0}}
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution (Z : W.IdealSheafData) (U V : W.affineOpens) (x : W) (hU : x ∈ U.1)
    (hV : x ∈ V.1) : (Z.ideal V).map (W.presheaf.germ V.1 x hV).hom =
      (Z.ideal U).map (W.presheaf.germ U.1 x hU).hom := by
  have hB : Opens.IsBasis W.affineOpens := by
    first
    | exact isBasis_affine_open W
    | exact isBasis_affineOpens W
    | exact W.isBasis_affineOpens
    | exact Scheme.isBasis_affineOpens W
    | exact AlgebraicGeometry.Scheme.isBasis_affine_open W
  obtain ⟨O, hO, hxO, hOle⟩ :=
    (Opens.isBasis_iff_nbhd.1 hB) (show x ∈ U.1 ⊓ V.1 from ⟨hU, hV⟩)
  let O' : W.affineOpens := ⟨O, hO⟩
  have hOU : O' ≤ U := fun y hy => (hOle hy).1
  have hOV : O' ≤ V := fun y hy => (hOle hy).2
  have key : ∀ (A : W.affineOpens) (hA : O' ≤ A) (hxA : x ∈ A.1),
      (Z.ideal A).map (W.presheaf.germ A.1 x hxA).hom =
        (Z.ideal O').map (W.presheaf.germ O x hxO).hom := by
    intro A hA hxA
    rw [← Z.map_ideal hA, Ideal.map_map, ← CommRingCat.hom_comp]
    congr 2
    exact (TopCat.Presheaf.germ_res _ _ _ _).symm
  rw [key V hOV hV, key U hOU hU]
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
