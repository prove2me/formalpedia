-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.valHom_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:29:58.429211+00:00
-- url     : https://prove2.me/submissions/c235745e-4776-4280-9104-91d2fbb13d8a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_unique
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_spec

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
theorem _root_.solution [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    valHom s x = (residueFieldIsoBase s x hx).hom.hom := by
  have hex : ∃ φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ :=
    ⟨_, valHom_spec s x hx⟩
  unfold valHom
  rw [dif_pos hex, valHom_unique s x hx _ hex.choose_spec]
end ReciprocityTheory.AnForm.R
