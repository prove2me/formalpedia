-- Prove2me | solution 1 for ThreeSum.TernaryOriginalAppendSemantics.append_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:22.253379+00:00
-- url     : https://prove2.me/submissions/93f7b418-33c5-418e-9fc8-b3d9ccbe3824

import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_ThreeSum_TernaryOriginalCollisions
import Definitions.Def_Submission_ThreeSum_TernaryOriginalAppendSemantics
import Theorems.Thm_ThreeSum_TernaryOriginalAppendSemantics_physical_hash
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_coefficientCode_append


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryOriginalAppendSemantics
open Finset TernaryOriginalRowMenu TernaryExtensionEncoding
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 3000000
namespace ThreeSum.TernaryOriginalAppendSemantics
theorem _root_.solution (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) {r J : ℕ}
    (raw : Fin (J+2)→ℤ) (z : ℕ→ℤ) (c : ℕ→ℕ) (previous : Fin r→ZMod p)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=(seedRow (J+2) ℓ seed (digitOrder J i)).val) :
    LightTernaryAppendKeys.key p (p^r) (J+2) (fun _ => coefficientCode previous) (fun _ => z) c 0=
      coefficientCode (appendVector previous (TernaryOriginalRowMenu.row (J+2) ℓ seed (fun i => (raw i : ZMod p)))) := by
  rw [coefficientCode_append]
  unfold LightTernaryAppendKeys.key
  rw [physical_hash ℓ seed J raw z c hz hzNonneg hc]
end ThreeSum.TernaryOriginalAppendSemantics
