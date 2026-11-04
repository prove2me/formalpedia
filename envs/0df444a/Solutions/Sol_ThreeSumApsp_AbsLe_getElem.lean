-- Prove2me | solution 1 for ThreeSumApsp.AbsLe.getElem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:16.505492+00:00
-- url     : https://prove2.me/submissions/d8afb8f5-230f-4749-9e71-f3267823a030

module
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.GetD
public import Mathlib.Data.Nat.Count
public import Definitions.Def_Submission_ThreeSumApsp_Util_List

set_option autoImplicit false
public section
open ThreeSumApsp
variable {α β : Type*}
namespace ThreeSumApsp
namespace AbsLe
theorem _root_.solution {l : List ℤ} {U : ℤ} (h : AbsLe l U) {i : ℕ} (hi : i < l.length) :
    |l[i]| ≤ U :=
  h _ (List.getElem_mem hi)
end AbsLe
end ThreeSumApsp
