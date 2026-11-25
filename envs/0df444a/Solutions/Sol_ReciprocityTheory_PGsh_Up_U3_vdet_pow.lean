-- Prove2me | solution 1 for ReciprocityTheory.PGsh.Up.U3.vdet_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:58:47.728038+00:00
-- url     : https://prove2.me/submissions/81809a40-5821-412f-a080-6efc5ca2b405

import Definitions.Def_ReciprocityTheory_DualLattices_ValuationDetEqOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_IsUnitDetOfSpanEq
import Definitions.Def_ReciprocityTheory_DualLattices_VIntCastLtOneOfDvd
import Definitions.Def_ReciprocityTheory_DualLattices_VdetLeOfSpanLe
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_sum_val
import Theorems.Thm_ReciprocityTheory_PGsh_Up_U3_vdet_vandermonde

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Up.U3
open ReciprocityTheory.PGsh.L2
variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {p : ℕ} [hp : Fact p.Prime]
namespace ReciprocityTheory.PGsh.Up.U3
theorem _root_.solution [NeZero p] (ω : ZMod p → C) (hω : ∀ a b, a ≠ b → v (ω a - ω b) = 1) (c : C) :
    v (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val).det = v c ^ (p * (p - 1) / 2) := by
  have e : (Matrix.of fun a j : ZMod p => (c * ω a) ^ j.val) =
      Matrix.of fun a j => c ^ j.val * (Matrix.of fun a j : ZMod p => ω a ^ j.val) a j := by
    ext a j
    simp [mul_pow]
  rw [e, Matrix.det_mul_row, map_mul, vdet_vandermonde ω hω, mul_one, map_prod]
  simp_rw [map_pow]
  rw [Finset.prod_pow_eq_pow_sum, sum_val]
end ReciprocityTheory.PGsh.Up.U3
