-- Prove2me | solution 1 for ThreeSum.TernaryExtensionEncoding.exists_monic_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:11:30.320015+00:00
-- url     : https://prove2.me/submissions/33796008-5f0f-45a5-86b0-ea83ea828cfe

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
namespace ThreeSum.TernaryExtensionEncoding
theorem _root_.solution (d : ℕ) (hd : 0<d) :
    ∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f.natDegree=d := by
  let E := GaloisField p d
  obtain ⟨a,ha⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) E
  have hi : IsIntegral (ZMod p) a := IsIntegral.of_finite (ZMod p) a
  refine ⟨minpoly (ZMod p) a,minpoly.monic hi,minpoly.irreducible hi,?_⟩
  have hn := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) a).mp ha
  exact hn.trans (GaloisField.finrank p (by omega))
end ThreeSum.TernaryExtensionEncoding
