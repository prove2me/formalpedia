-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_exact_be2abbfe586b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:29.091948+00:00
-- url     : https://prove2.me/submissions/2eb2f3cd-7b97-4db0-9278-77971628a486

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_free_away_mul_b70e4fea877c

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
namespace IsGenericallyFree
theorem _root_.solution [IsDomain A] {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module A N₁]
    [AddCommGroup N₂] [Module A N₂] [AddCommGroup N₃] [Module A N₃] (i : N₁ →ₗ[A] N₂) (p : N₂ →ₗ[A] N₃)
    (hi : Function.Injective i) (hp : Function.Surjective p) (hex : Function.Exact i p)
    (h₁ : IsGenericallyFree A N₁) (h₃ : IsGenericallyFree A N₃) : IsGenericallyFree A N₂ := by
  obtain ⟨f₁, hf₁, hfree₁⟩ := h₁
  obtain ⟨f₃, hf₃, hfree₃⟩ := h₃
  have free₁ := free_away_mul f₃ hfree₁
  have free₃ := free_away_mul f₁ hfree₃
  rw [mul_comm f₃ f₁] at free₃
  set f := f₁ * f₃
  refine ⟨f, mul_ne_zero hf₁ hf₃, ?_⟩
  let S := Submonoid.powers f
  let iL : LocalizedModule S N₁ →ₗ[Localization.Away f] LocalizedModule S N₂ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₁) (LocalizedModule.mkLinearMap S N₂) i).extendScalarsOfIsLocalization S (Localization.Away f)
  let pL : LocalizedModule S N₂ →ₗ[Localization.Away f] LocalizedModule S N₃ :=
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S N₂) (LocalizedModule.mkLinearMap S N₃) p).extendScalarsOfIsLocalization S (Localization.Away f)
  have ex : Function.Exact iL pL := LocalizedModule.map_exact S i p hex
  have hiL : Function.Injective iL := IsLocalizedModule.map_injective S _ _ i hi
  have hpL : Function.Surjective pL := IsLocalizedModule.map_surjective S _ _ p hp
  obtain ⟨s, hs⟩ := Module.projective_lifting_property pL LinearMap.id hpL
  exact Module.Free.of_equiv (ex.splitSurjectiveEquiv hiL ⟨s, hs⟩).1.symm
end IsGenericallyFree
end GroundTheory.Heights₂.Heights.GenericFreeness
