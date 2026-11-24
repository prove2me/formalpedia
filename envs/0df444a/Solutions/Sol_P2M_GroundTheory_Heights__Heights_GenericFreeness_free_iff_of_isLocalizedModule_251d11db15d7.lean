-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:53:26.049023+00:00
-- url     : https://prove2.me/submissions/4bd6c82f-fe1c-48c3-a2eb-fe96f0a0edae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.GenericFreeness
open Module
universe u
variable {A : Type u} [CommRing A]
namespace GroundTheory.Heights₂.Heights.GenericFreeness
theorem _root_.solution (f : A) {M N : Type*} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module A N] (g : M →ₗ[A] N) [IsLocalizedModule (Submonoid.powers f) g]
    (Rf : Type*) [CommRing Rf] [Algebra A Rf] [IsLocalization.Away f Rf] [Module Rf N]
    [IsScalarTower A Rf N] :
    Module.Free Rf N ↔ Module.Free (Localization.Away f) (LocalizedModule (Submonoid.powers f) M) := by
  let e₁ : Localization.Away f ≃+* Rf :=
    (IsLocalization.algEquiv (Submonoid.powers f) (Localization.Away f) Rf).toRingEquiv
  let e₂ : LocalizedModule (Submonoid.powers f) M ≃ₗ[A] N := IsLocalizedModule.iso _ g
  have key : ∀ (r : Localization.Away f) (x : LocalizedModule (Submonoid.powers f) M),
      e₂ (r • x) = e₁ r • e₂ x := by
    intro r x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) r
    have hs := IsLocalizedModule.map_units g s
    rw [Module.End.isUnit_iff] at hs
    apply hs.1
    simp only [Module.algebraMap_end_apply]
    have h1 : (s : A) • IsLocalization.mk' (Localization.Away f) a s = algebraMap A _ a := by
      rw [Algebra.smul_def, IsLocalization.mk'_spec']
    have h2 : (s : A) • e₁ (IsLocalization.mk' (Localization.Away f) a s) = algebraMap A Rf a := by
      have : e₁ (IsLocalization.mk' (Localization.Away f) a s) = IsLocalization.mk' Rf a s :=
        IsLocalization.algEquiv_mk' _ _
      rw [this, Algebra.smul_def, IsLocalization.mk'_spec']
    rw [← map_smul, ← smul_assoc, h1, algebraMap_smul, ← smul_assoc, h2, algebraMap_smul, map_smul]
  haveI := RingHomInvPair.of_ringEquiv e₁
  haveI := RingHomInvPair.of_ringEquiv_symm e₁
  let e : LinearEquiv (e₁ : Localization.Away f →+* Rf) (LocalizedModule (Submonoid.powers f) M) N :=
    { e₂.toAddEquiv with map_smul' := fun r x ↦ key r x }
  exact (Module.Free.iff_of_equiv e).symm
end GroundTheory.Heights₂.Heights.GenericFreeness
