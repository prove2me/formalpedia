-- Prove2me | solution 1 for closure_numericalRange_smul_add_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:44:09.532794+00:00
-- url     : https://prove2.me/submissions/8c73fc2c-980c-49c2-a470-b7b0b1d73f69

import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_AffineClosure
import Theorems.Thm_numericalRange_smul_add_smul_one

set_option autoImplicit false
open Set
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    closure (numericalRange (a • A + b • 1)) =
      (fun z => a * z + b) '' closure (numericalRange A) := by
  rw [numericalRange_smul_add_smul_one]
  let e : ℂ ≃ₜ ℂ :=
    (Homeomorph.mulLeft₀ a ha).trans (Homeomorph.addRight b)
  have h := (e.image_closure (numericalRange A)).symm
  have he : (e : ℂ → ℂ) = fun z => a * z + b := by
    funext z
    rfl
  rw [he] at h
  exact h
