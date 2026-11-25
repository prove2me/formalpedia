-- Prove2me | solution 1 for ReciprocityTheory.CA.isCMMod_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:39.08408+00:00
-- url     : https://prove2.me/submissions/5416a553-9f21-49dc-8eb6-88bf90422c74

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Theorems.Thm_ReciprocityTheory_CA_modDepthGE_congr

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.CA
open IsLocalRing RingTheory.Sequence
variable {R : Type*} [CommRing R] [IsLocalRing R]
namespace ReciprocityTheory.CA
theorem _root_.solution {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) : IsCMMod R M ↔ IsCMMod R N := by
  have hs : Module.support R M = Module.support R N :=
    (Module.support_subset_of_injective e.toLinearMap e.injective).antisymm
      (Module.support_subset_of_surjective e.toLinearMap e.surjective)
  have hd : Module.supportDim R M = Module.supportDim R N := by
    unfold Module.supportDim
    rw [hs]
  constructor
  · rintro ⟨h1, h2, n, hn, h3⟩
    exact ⟨h1, Module.Finite.equiv e, n, hd.symm.trans hn, (modDepthGE_congr e n).mp h3⟩
  · rintro ⟨h1, h2, n, hn, h3⟩
    exact ⟨h1, Module.Finite.equiv e.symm, n, hd.trans hn, (modDepthGE_congr e n).mpr h3⟩
end ReciprocityTheory.CA
