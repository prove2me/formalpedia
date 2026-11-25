-- Prove2me | solution 1 for ReciprocityTheory.CA.modDepthGE_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:47.638256+00:00
-- url     : https://prove2.me/submissions/cf2bada3-d912-48ff-bfad-ced735750f16

import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_ModDepthGE
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge

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
    (e : M ≃ₗ[R] N) (n : ℕ) : ModDepthGE R M n ↔ ModDepthGE R N n := by
  constructor
  · rintro ⟨rs, h1, h2, h3⟩
    exact ⟨rs, h1, h2, (e.isRegular_congr rs).mp h3⟩
  · rintro ⟨rs, h1, h2, h3⟩
    exact ⟨rs, h1, h2, (e.isRegular_congr rs).mpr h3⟩
end ReciprocityTheory.CA
