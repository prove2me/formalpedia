-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.constantCoefficient_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:16:03.715965+00:00
-- url     : https://prove2.me/submissions/c8e14375-d7a8-4b61-aaf8-214642026dcb

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Digits.Lemmas
import Definitions.Def_Submission_ThreeSum_TernaryExtensionEncoding
import Theorems.Thm_ThreeSum_TernaryExtensionEncoding_constantCoefficient_surjective

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryExtensionEncoding
open Polynomial
set_option maxHeartbeats 3000000
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) : constantCoefficient hf hd≠0 := by
  intro h
  obtain ⟨x,hx⟩ := constantCoefficient_surjective hf hd (1 : ZMod p)
  rw [h,LinearMap.zero_apply] at hx
  exact zero_ne_one hx
end ThreeSum.TernaryExtensionEncoding
