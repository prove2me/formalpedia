-- Prove2me | solution 1 for ReciprocityTheory.Neutral.Bridge.bijective_of_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:16:30.145574+00:00
-- url     : https://prove2.me/submissions/fa2d494c-b101-493a-80f0-f79ab5783ac7

import Definitions.Def_ReciprocityTheory_Hypotheses_GalCohDefs
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_TransportA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.Neutral ReciprocityTheory.Neutral.Bridge
open ReciprocityTheory.Gal
variable {R : Type*} [CommRing R] {A A' B B' C C' : Type*}
  [AddCommGroup A] [Module R A] [AddCommGroup A'] [Module R A']
  [AddCommGroup B] [Module R B] [AddCommGroup B'] [Module R B']
  [AddCommGroup C] [Module R C] [AddCommGroup C'] [Module R C']
namespace ReciprocityTheory.Neutral.Bridge
theorem _root_.solution (α : A ≃ₗ[R] A') (β : B ≃ₗ[R] B') (γ : C ≃ₗ[R] C')
    (f : A →ₗ[R] B →ₗ[R] C) (f' : A' →ₗ[R] B' →ₗ[R] C')
    (h : ∀ a b, f' (α a) (β b) = γ (f a b)) (hf : Function.Bijective f') :
    Function.Bijective f := by
  let Φ : (B →ₗ[R] C) ≃ₗ[R] (B' →ₗ[R] C') := LinearEquiv.arrowCongr β γ
  have key : ∀ a, f a = Φ.symm (f' (α a)) := by
    intro a
    apply Φ.injective
    rw [LinearEquiv.apply_symm_apply]
    ext b'
    rw [LinearEquiv.arrowCongr_apply, ← h, LinearEquiv.apply_symm_apply]
  have hfun : (⇑f) = ⇑Φ.symm ∘ ⇑f' ∘ ⇑α := funext key
  rw [hfun]
  exact Φ.symm.bijective.comp (hf.comp α.bijective)
end ReciprocityTheory.Neutral.Bridge
