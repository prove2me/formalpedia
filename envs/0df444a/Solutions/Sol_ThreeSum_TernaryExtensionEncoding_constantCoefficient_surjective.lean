-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.constantCoefficient_surjective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:31.457284+00:00
-- url     : https://prove2.me/submissions/7ce1e2d6-3005-4e6e-9ded-a4a61033b40b

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
theorem _root_.solution {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) : Function.Surjective (constantCoefficient hf hd) := by
  intro a
  refine ⟨(coefficients hf).symm (fun _ => a),?_⟩
  simp [constantCoefficient]
end ThreeSum.TernaryExtensionEncoding
