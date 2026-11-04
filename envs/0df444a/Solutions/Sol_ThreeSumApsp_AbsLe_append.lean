-- Prove2me | solution 1 for ThreeSumApsp.AbsLe.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:18.187291+00:00
-- url     : https://prove2.me/submissions/8f218a41-d654-431f-b5fc-0fae2027b7d4

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
theorem _root_.solution {l₁ l₂ : List ℤ} {U : ℤ} (h₁ : AbsLe l₁ U) (h₂ : AbsLe l₂ U) :
    AbsLe (l₁ ++ l₂) U :=
  List.forall_mem_append.2 ⟨h₁, h₂⟩
end AbsLe
end ThreeSumApsp
