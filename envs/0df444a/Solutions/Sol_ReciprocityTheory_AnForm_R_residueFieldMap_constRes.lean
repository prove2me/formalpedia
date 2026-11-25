-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.residueFieldMap_constRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:09:16.841799+00:00
-- url     : https://prove2.me/submissions/a8772350-152a-4974-b0fa-265640b53fe4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso

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
variable {S : Scheme.{0}} (s : S ⟶ Spec (CommRingCat.of ℂ))
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ℂ)) (g : S ⟶ T)
    (hg : g ≫ t = s) (x : S) :
    (g.residueFieldMap x).hom.comp (constRes t (g.base x)) = constRes s x := by
  have hA : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)), y.appLE ⊤ ⊤ le_top = y.appTop :=
    fun Y y => (y.app_eq_appLE (U := ⊤)).symm
  have hc : ∀ (Y : Scheme.{0}) (y : Y ⟶ Spec (CommRingCat.of ℂ)) (z : Y), constRes y z =
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ y.appTop ≫ Y.evaluation ⊤ z trivial).hom := by
    intro Y y z
    rw [← hA]; rfl
  rw [hc, hc, ← CommRingCat.hom_comp]
  congr 1
  simp only [Category.assoc]
  rw [Scheme.evaluation_naturality g x (V := ⊤) trivial, ← hg, Scheme.Hom.comp_appTop,
    Category.assoc]
  rfl
end ReciprocityTheory.AnForm.R
