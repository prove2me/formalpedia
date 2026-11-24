-- Prove2me | solution 1 for P2M_Kirkman_SteinerOp_op_op_right__bbbfe2541011
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:43:00.957068+00:00
-- url     : https://prove2.me/submissions/cdfcf645-d6fb-48d5-a33d-5ccfd2115a92

module
public import Mathlib
public import Definitions.Def_KirkmanLib_SteinerOp
public import Theorems.Thm_Kirkman_SteinerOp_op_op_right

set_option autoImplicit true
@[expose] public section
public section
open Finset
open Kirkman
variable {P : Type*}
open Kirkman.SteinerOp
variable (S : SteinerOp P)
variable [DecidableEq P]
omit [DecidableEq P]
namespace Kirkman.SteinerOp
theorem _root_.solution (x y : P) : S.op (S.op x y) y = x := by rw [S.comm, S.op_op_right]
end Kirkman.SteinerOp
