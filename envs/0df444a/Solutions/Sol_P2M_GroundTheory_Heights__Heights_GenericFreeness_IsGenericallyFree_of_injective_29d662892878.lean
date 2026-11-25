-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_IsGenericallyFree_of_injective_29d662892878
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:46:29.831066+00:00
-- url     : https://prove2.me/submissions/0b4c865a-795b-46c2-8311-202553bd6de7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessLoc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_free_iff_of_isLocalizedModule_251d11db15d7
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
theorem _root_.solution [IsDomain A] {N M : Type*} [AddCommGroup N] [Module A N] [AddCommGroup M]
    [Module A M] (i : N →ₗ[A] M) (hi : Function.Injective i) (a : A) (ha : a ≠ 0)
    (hsat : ∀ m : M, ∃ k : ℕ, a ^ k • m ∈ LinearMap.range i) (hN : IsGenericallyFree A N) :
    IsGenericallyFree A M := by
  obtain ⟨f, hf, hfree⟩ := hN
  have hfree' := free_away_mul a hfree
  set F := f * a with hF
  refine ⟨F, mul_ne_zero hf ha, ?_⟩
  haveI : IsLocalizedModule (Submonoid.powers F) (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) := by
    constructor
    · exact IsLocalizedModule.map_units (LocalizedModule.mkLinearMap (Submonoid.powers F) M)
    · intro y
      obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (Submonoid.powers F)
        (LocalizedModule.mkLinearMap (Submonoid.powers F) M) y
      obtain ⟨k, n, hn⟩ := hsat m
      refine ⟨⟨f ^ k • n, ⟨F ^ k, k, rfl⟩ * s⟩, ?_⟩
      simp only [Submonoid.smul_def, Submonoid.coe_mul, LinearMap.coe_comp, Function.comp_apply,
        map_smul, hn] at hms ⊢
      rw [mul_smul, hms, ← map_smul, smul_smul, hF, mul_pow]
      exact map_smul _ _ _
    · intro n₁ n₂ e
      obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers F)
        (f := LocalizedModule.mkLinearMap (Submonoid.powers F) M) e
      refine ⟨c, hi ?_⟩
      simpa only [Submonoid.smul_def, map_smul] using hc
  exact (free_iff_of_isLocalizedModule F
    (LocalizedModule.mkLinearMap (Submonoid.powers F) M ∘ₗ i) (Localization.Away F)).2 hfree'
end IsGenericallyFree
end GroundTheory.Heights₂.Heights.GenericFreeness
