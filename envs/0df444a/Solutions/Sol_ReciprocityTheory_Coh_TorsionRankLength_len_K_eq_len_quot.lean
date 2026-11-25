-- Prove2me | solution 1 for ReciprocityTheory.Coh.TorsionRankLength.len_K_eq_len_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:57:37.458276+00:00
-- url     : https://prove2.me/submissions/f7098c34-73a7-4d82-aed8-b30228af0775

import Mathlib
import Definitions.Def_ReciprocityTheory_GroupCohomology_RankLenA
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_smul_top_eq_range
import Theorems.Thm_ReciprocityTheory_Coh_TorsionRankLength_len_sub_add_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.Coh ReciprocityTheory.Coh.TorsionRankLength
universe u
open Module Submodule Function
open scoped Pointwise TensorProduct
variable {R : Type u} [CommRing R] {M : Type u} [AddCommGroup M] [Module R M]
namespace ReciprocityTheory.Coh.TorsionRankLength
theorem _root_.solution (hM : IsFiniteLength R M) (r : R) :
    Module.length R (K M r) = Module.length R (QuotSMulTop r M) := by
  set φ : M →ₗ[R] M := r • LinearMap.id with hφ
  have h1 : Module.length R M = Module.length R (K M r) + Module.length R (LinearMap.range φ) :=
    Module.length_eq_add_of_exact (K M r).subtype φ.rangeRestrict (Submodule.injective_subtype _)
      φ.surjective_rangeRestrict
      (LinearMap.exact_iff.2 (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
  have h2 : Module.length R M = Module.length R (r • ⊤ : Submodule R M) + Module.length R (QuotSMulTop r M) :=
    len_sub_add_quot (r • ⊤ : Submodule R M)
  have h3 : Module.length R (r • ⊤ : Submodule R M) = Module.length R (LinearMap.range φ) :=
    (LinearEquiv.ofEq _ _ (smul_top_eq_range r)).length_eq
  have hMt : Module.length R M ≠ ⊤ := Module.length_ne_top_iff.2 hM
  have hL : Module.length R (LinearMap.range φ) ≠ ⊤ := fun h => hMt (by rw [h1, h, add_top])
  rw [h3] at h2
  rw [h1, add_comm (Module.length R (LinearMap.range φ))] at h2
  exact WithTop.add_right_cancel hL h2
end ReciprocityTheory.Coh.TorsionRankLength
