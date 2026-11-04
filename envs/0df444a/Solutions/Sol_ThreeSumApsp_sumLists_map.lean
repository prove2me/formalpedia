-- Prove2me | solution 1 for ThreeSumApsp.sumLists_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:36:20.081342+00:00
-- url     : https://prove2.me/submissions/0eb3ffd2-20cb-4850-a9df-e6f25322ebc6

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
theorem _root_.solution (l : List α) (ts : List β) (f : β → α → ℤ) :
    sumLists l.length (ts.map fun t => l.map (f t)) =
      l.map fun c => (ts.map fun t => f t c).sum := by
  have hfold : ∀ (ts : List β) (g : α → ℤ),
      (ts.map fun t => l.map (f t)).foldl (fun acc l' => List.zipWith (· + ·) acc l') (l.map g) =
        l.map fun c => g c + (ts.map fun t => f t c).sum := by
    intro ts
    induction ts with
    | nil => simp
    | cons t ts ih =>
      intro g
      rw [List.map_cons, List.foldl_cons, List.zipWith_map, List.zipWith_self, ih]
      simp only [List.map_cons, List.sum_cons, add_assoc]
  rw [sumLists, ← List.map_const', hfold]
  simp only [zero_add]
end ThreeSumApsp
