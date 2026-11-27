-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.existsUnique_valHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:23:45.195785+00:00
-- url     : https://prove2.me/submissions/e45b5ce6-8b13-4072-92ee-bd20bc4e958c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FromSpecResidueFieldAppTopIso
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_unique
import Theorems.Thm_ReciprocityTheory_AnForm_R_valHom_spec
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
theorem _root_.solution [LocallyOfFiniteType s] (x : S) (hx : IsClosed ({x} : Set S)) :
    (∃! φ : S.residueField x →+* ℂ, φ.comp (constRes s x) = RingHom.id ℂ) ∧
      Function.Bijective (valHom s x) := by
  refine ⟨⟨_, valHom_spec s x hx, fun ψ hψ => valHom_unique s x hx ψ hψ⟩, ?_⟩
  rw [valHom_eq s x hx]
  exact (residueFieldIsoBase s x hx).commRingCatIsoToRingEquiv.bijective
end ReciprocityTheory.AnForm.R
