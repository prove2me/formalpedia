-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.valHom_unique
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:23:53.82224+00:00
-- url     : https://prove2.me/submissions/7c730924-9766-419e-9497-7a67d7a60759

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
theorem _root_.solution [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S))
    (ψ : S.residueField x →+* ℂ) (h : ψ.comp (constRes s x) = RingHom.id ℂ) :
    ψ = (residueFieldIsoBase s x hx).hom.hom := by
  ext y
  have h1 : (residueFieldIsoBase s x hx).inv.hom ((residueFieldIsoBase s x hx).hom.hom y) = y := by
    rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
      RingHom.id_apply]
  have h2 := congrArg (fun f : ℂ →+* ℂ => f ((residueFieldIsoBase s x hx).hom.hom y)) h
  simp only [RingHom.comp_apply, RingHom.id_apply, constRes_eq s x hx, h1] at h2
  exact h2
end ReciprocityTheory.AnForm.R
