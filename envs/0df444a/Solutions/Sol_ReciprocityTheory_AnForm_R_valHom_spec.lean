-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.valHom_spec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:45.177391+00:00
-- url     : https://prove2.me/submissions/a284d791-2e5e-43c1-8592-d3d92c033ba6

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_constRes_eq

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
    ((residueFieldIsoBase s x hx).hom.hom).comp (constRes s x) = RingHom.id ℂ := by
  rw [constRes_eq s x hx, ← CommRingCat.hom_comp, Iso.inv_hom_id, CommRingCat.hom_id]
end ReciprocityTheory.AnForm.R
