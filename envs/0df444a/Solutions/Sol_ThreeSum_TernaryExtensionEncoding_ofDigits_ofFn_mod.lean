-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.ofDigits_ofFn_mod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:32.625269+00:00
-- url     : https://prove2.me/submissions/090c0f67-f0cd-440a-8b32-0f9068f48b83

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
set_option maxHeartbeats 3000000
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {d : ℕ} (hd : 0<d) (a : Fin d → ℕ) :
    Nat.ofDigits p (List.ofFn a)%p=a ⟨0,hd⟩%p := by
  cases d with
  | zero => omega
  | succ d => simp [List.ofFn_succ,Nat.ofDigits_cons,Nat.add_mod]
end ThreeSum.TernaryExtensionEncoding
