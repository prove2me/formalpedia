-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.append_original_key
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:43:22.156798+00:00
-- url     : https://prove2.me/submissions/b108ed71-aa2f-4407-83c4-9c7558d790d4

import Definitions.Def_Submission_ThreeSum_TernaryExtensionSeedSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryAppendKeys
import Definitions.Def_Submission_ThreeSum_TernarySignedLayout
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_coefficientCode_append
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_physical_original_hash

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
variable {f : (ZMod p)[X]} [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (hf : f.Monic) (hd : 0<f.natDegree) {r J : ℕ}
    (x y : AdjoinRoot f) (raw : Fin (J+2) → ℤ) (z : ℕ → ℤ) (c : ℕ → ℕ)
    (previous : Fin r → ZMod p)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i)).val) :
    LightTernaryAppendKeys.key p (p^r) (J+2) (fun _ => coefficientCode previous)
      (fun _ => z) c 0=
      coefficientCode (appendVector previous
        (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
          (fun i => (raw i : ZMod p)))) := by
  rw [coefficientCode_append]
  unfold LightTernaryAppendKeys.key
  rw [physical_original_hash hf hd J x y raw z c hz hzNonneg hc]
end ThreeSum.TernaryExtensionEncoding
