-- Prove2me | solution 1 for P2M_GlobalTheory_Avoid_pairingDual__Multi_comp_bbdba73fb990
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:50:21.992056+00:00
-- url     : https://prove2.me/submissions/8a2b409c-bc59-4b6f-9ebe-b1ece304144e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower
namespace GlobalTheory.Avoid
theorem _root_.solution {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] {r : ℕ} (φ : M →ₗ[R] N) (f : Fin r → Dual R N)
    (x : ⋀[R]^r M) :
    pairingDual R M r (ιMulti R r fun k => f k ∘ₗ φ) x =
      pairingDual R N r (ιMulti R r f) (exteriorPower.map r φ x) := by
  have : pairingDual R M r (ιMulti R r fun k => f k ∘ₗ φ) =
      pairingDual R N r (ιMulti R r f) ∘ₗ exteriorPower.map r φ := by
    apply exteriorPower.linearMap_ext
    ext v
    simp [pairingDual_ιMulti_ιMulti]
  rw [this, LinearMap.comp_apply]
end GlobalTheory.Avoid
