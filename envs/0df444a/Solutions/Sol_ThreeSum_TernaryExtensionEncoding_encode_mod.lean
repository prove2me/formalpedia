-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.encode_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:04.963741+00:00
-- url     : https://prove2.me/submissions/be43cfe4-c014-4ada-be32-b96cc7cdb054

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_ofDigits_ofFn_mod

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
set_option maxHeartbeats 3000000
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic) (hd : 0<f.natDegree)
    (x : AdjoinRoot f) : encode hf x%p=(constantCoefficient hf hd x).val := by
  rw [encode,ofDigits_ofFn_mod hd]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
  rfl
end ThreeSum.TernaryExtensionEncoding
