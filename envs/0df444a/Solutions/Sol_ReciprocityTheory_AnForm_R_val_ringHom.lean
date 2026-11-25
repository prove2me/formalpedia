-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.val_ringHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:36:47.623927+00:00
-- url     : https://prove2.me/submissions/e36587d6-f245-4f0d-9902-d99843656b36

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_eq

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
theorem _root_.solution [LocallyOfFiniteType s] (U : S.Opens) (x : S) (hx : x ∈ U)
    (hc : IsClosed ({x} : Set S)) :
    ∃ φ : Γ(S, U) →+* ℂ, ∀ f, φ f = val s f x hx := by
  refine ⟨(residueFieldIsoBase s x hc).hom.hom.comp (S.evaluation U x hx).hom, fun f => ?_⟩
  unfold val
  rw [valHom_eq s x hc]
  rfl
end ReciprocityTheory.AnForm.R
