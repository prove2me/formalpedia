-- Prove2me | solution 1 for P2M_Nat_div_lt_of_lt_mul__63b09184c268
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:34:16.432422+00:00
-- url     : https://prove2.me/submissions/0d85695d-0516-49d4-ba3f-8443d5a051f7

module
public import Mathlib.Algebra.Order.Ring.Int
public import Definitions.Def_Submission_ThreeSumApsp_Util_Index

set_option autoImplicit false
public section
open Nat
namespace Nat
theorem _root_.solution {t m n : ℕ} (h : t < m * n) : t / n < m :=
  Nat.div_lt_of_lt_mul (Nat.mul_comm m n ▸ h)
end Nat
