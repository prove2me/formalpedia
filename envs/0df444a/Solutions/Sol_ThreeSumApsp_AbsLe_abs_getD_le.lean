-- Prove2me | solution 1 for ThreeSumApsp.AbsLe.abs_getD_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:19.08557+00:00
-- url     : https://prove2.me/submissions/10c7487c-10fe-469e-b74a-faf0b0609e30

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List
public import Theorems.Thm_List_getD_of_forall_mem

set_option autoImplicit false
public section
open ThreeSumApsp
variable {α β : Type*}
namespace ThreeSumApsp
namespace AbsLe
theorem _root_.solution {l : List ℤ} {U : ℤ} (hU : 0 ≤ U) (h : AbsLe l U) (i : ℕ) :
    |l.getD i 0| ≤ U :=
  List.getD_of_forall_mem (p := fun x => |x| ≤ U) (by rwa [abs_zero]) h i
end AbsLe
end ThreeSumApsp
