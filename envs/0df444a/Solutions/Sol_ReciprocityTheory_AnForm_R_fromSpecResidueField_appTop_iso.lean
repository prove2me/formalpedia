-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.fromSpecResidueField_appTop_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:35.347202+00:00
-- url     : https://prove2.me/submissions/86086e91-d37d-440c-b189-81e12546146f

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
theorem _root_.solution (x : S) :
    (S.fromSpecResidueField x).appTop ≫ (Scheme.ΓSpecIso _).hom = S.evaluation ⊤ x trivial := by
  simp only [Scheme.fromSpecResidueField, Scheme.Hom.comp_appTop, Category.assoc,
    Scheme.ΓSpecIso_naturality, Scheme.fromSpecStalk_appTop, Scheme.evaluation]
  have hid : (Spec (S.presheaf.stalk x)).presheaf.map
      (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ := by
    rw [show (homOfLE (le_top : (⊤ : (Spec (S.presheaf.stalk x)).Opens) ≤ ⊤)).op = 𝟙 _ from rfl,
      CategoryTheory.Functor.map_id]
  simp [hid]
end ReciprocityTheory.AnForm.R
