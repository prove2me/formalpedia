-- Prove2me | solution 1 for SemigroupBetti.GenData.beta1_le_two_w
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:25:56.674273+00:00
-- url     : https://prove2.me/submissions/d63f4ad0-757d-471a-98c0-8e3f743a5fca

module
public import Definitions.Def_SemigroupBetti_Exceptional
public import Definitions.Def_SemigroupBetti_Main
public import Theorems.Thm_SemigroupBetti_GenData_beta1_le_two_W
public import Theorems.Thm_SemigroupBetti_GenData_W_le_w


set_option autoImplicit false
@[expose] public section
public section
open SemigroupBetti
open SemigroupBetti.GenData
variable (G : GenData)
namespace SemigroupBetti.GenData
theorem _root_.solution : G.beta1 ≤ 2 * G.w :=
  G.beta1_le_two_W.trans (Nat.mul_le_mul_left 2 G.W_le_w)
end SemigroupBetti.GenData
