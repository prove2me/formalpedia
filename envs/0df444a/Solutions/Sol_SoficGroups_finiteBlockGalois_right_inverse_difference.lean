-- Prove2me | solution 1 for SoficGroups.finiteBlockGalois_right_inverse_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:54.580336+00:00
-- url     : https://prove2.me/submissions/28eb2293-a835-4635-96fd-5e245f358313

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open scoped BigOperators commutatorElement
variable {R : Type*} [Ring R] [Algebra (ZMod 2) R]
namespace SoficGroups
theorem _root_.solution
    (s t : finiteBlockGaloisField) (hst : s ≠ t)
    (C : Matrix (Fin 3) (Fin 3) R) :
    (C * finiteBlockGaloisMatrixOver R (t - s)⁻¹) *
        finiteBlockGaloisMatrixOver R t -
      (C * finiteBlockGaloisMatrixOver R (t - s)⁻¹) *
        finiteBlockGaloisMatrixOver R s = C := by
  rw [← mul_sub, ← map_sub, mul_assoc, ← map_mul,
    inv_mul_cancel₀ (sub_ne_zero.mpr hst.symm), map_one, mul_one]
end SoficGroups
