-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck_of_frontier
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T21:04:26.344654+00:00
-- url     : https://prove2.me/submissions/530a6d00-9a57-438c-9dcb-9370701891d2

import Definitions.Def_Sensitivity213981Formal_Endpoint22FastTree
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto


namespace Sensitivity213981Formal
section

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundRankCached ThreeBoundRankAnnotated





theorem Tree.fastCheck_branch (deny q : ℕ) (values : CostValues) (bound bits : ℕ)
    (pivot : List ℕ) (left right : ThreeBoundRankAnnotated.Tree)
    (hl : Tree.fastCheck deny q values bound left=true)
    (hr : Tree.fastCheck deny q values bound right=true) :
    Tree.fastCheck deny q values bound (.branch bits pivot left right)=true := by
  simp only [Tree.fastCheck]
  split
  · rfl
  · simp only [hl,hr,Bool.true_and]

theorem Tree.fastCheck_of_frontier (deny q : ℕ) (values : CostValues)
    (bound depth : ℕ) (t : ThreeBoundRankAnnotated.Tree)
    (h : (t.frontier depth).all (fun s => Tree.fastCheck deny q values bound s)=true) :
    Tree.fastCheck deny q values bound t=true := by
  induction depth generalizing t with
  | zero => simpa only [ThreeBoundRankAnnotated.Tree.frontier,List.all_cons,List.all_nil,Bool.and_true] using h
  | succ depth ih =>
      cases t with
      | leaf bits key code =>
          simpa only [ThreeBoundRankAnnotated.Tree.frontier,List.all_cons,List.all_nil,Bool.and_true] using h
      | branch bits pivot left right =>
          have hh : (left.frontier depth).all (fun s => Tree.fastCheck deny q values bound s)=true ∧
              (right.frontier depth).all (fun s => Tree.fastCheck deny q values bound s)=true := by
            simpa only [ThreeBoundRankAnnotated.Tree.frontier,List.all_append,Bool.and_eq_true] using h
          exact Tree.fastCheck_branch deny q values bound bits pivot left right
            (ih left hh.1) (ih right hh.2)

end ThreeBoundEndpoint22Packed


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (deny q : Nat) (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound depth : Nat)
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (h :
    @Eq.{1} Bool
      (@List.all.{0} Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree
        (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.frontier t depth)
        fun (s : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree) =>
        Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck deny q values bound s)
      Bool.true),
  @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck deny q values bound t) Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck_of_frontier
