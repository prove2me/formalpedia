-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck_of_dominance
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:57:26.954386+00:00
-- url     : https://prove2.me/submissions/1a875551-a832-496c-a4bf-e8b25b247d39

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankCoefficientDominance
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
/- Certified common-kind masks skip whole impossible record subtrees. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 200000
namespace ThreeBoundRankAnnotated
open ThreeBoundNumeric (Caps recordOfList)
open ThreeBoundRankNumeric ThreeBoundRankCached ThreeBoundFullProfile
open ThreeBoundEndpoint22Records

theorem and_true {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h





































end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Reuse an exact record certificate when every normalized cost decreases. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundRankAnnotated
open ThreeBoundRankCached ThreeBoundRankNumeric
open ThreeBoundEndpoint22Records





theorem headSum_cross_le (q : ℕ) (x y : CostValues) (a b : ℕ)
    (h : CoefficientLe q x y a b) (r : Record) : headSum x r*b≤ headSum y r*a := by
  simp only [headSum,List.ofFn_eq_map]
  rw [← List.sum_map_mul_right,← List.sum_map_mul_right]
  apply List.sum_le_sum
  intro k hk
  simp only [Nat.add_mul,Nat.mul_assoc]
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · exact Nat.mul_le_mul_left _ (h.heads ⟨3*k.val,by omega⟩)
    · exact Nat.mul_le_mul_left _ (h.heads ⟨3*k.val+1,by omega⟩)
  · exact Nat.mul_le_mul_left _ (h.heads ⟨3*k.val+2,by omega⟩)

theorem preparedCost_cross_le (q : ℕ) (p : PreparedValues) (x y : CostValues)
    (a b : ℕ) (h : CoefficientLe q x y a b) (r : Record) (e : ℕ) :
    preparedCost q p x r e*b≤ preparedCost q p y r e*a := by
  have hn : ((List.range (q+1)).map fun k => readNegative p e k*x.negative.getD k 0).sum*b≤ 
      ((List.range (q+1)).map fun k => readNegative p e k*y.negative.getD k 0).sum*a := by
    rw [← List.sum_map_mul_right,← List.sum_map_mul_right]
    apply List.sum_le_sum
    intro k hk
    simpa only [Nat.mul_assoc] using
      Nat.mul_le_mul_left (readNegative p e k) (h.negative ⟨k,List.mem_range.mp hk⟩)
  have hg : ((r 11-e)*x.guard)*b≤ ((r 11-e)*y.guard)*a := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left (r 11-e) h.guard
  have he : (e*x.converted)*b≤ (e*y.converted)*a := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left e h.converted
  simpa only [preparedCost,Nat.add_mul] using
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hg he) hn) (headSum_cross_le q x y a b h r)

theorem preparedCost_bound_of_dominance (q : ℕ) (p : PreparedValues) (x y : CostValues)
    (a b : ℕ) (hb : 0< b) (h : CoefficientLe q x y a b) (r : Record) (e : ℕ)
    (hy : preparedCost q p y r e≤ b) : preparedCost q p x r e≤ a := by
  apply Nat.le_of_mul_le_mul_right (c:=b) _ hb
  exact (preparedCost_cross_le q p x y a b h r e).trans
    (by simpa only [Nat.mul_comm] using Nat.mul_le_mul_right a hy)





theorem blocked_of_maskLe (small large : Array Bool) (h : MaskLe small large)
    (bits : ℕ) (hb : blocked large bits=true) : blocked small bits=true := by
  obtain ⟨k,hk,hbits⟩ := List.any_eq_true.mp hb
  obtain ⟨hbit,hnot⟩ := and_true hbits
  apply List.any_eq_true.mpr
  refine ⟨k,hk,?_⟩
  cases hs : small.getD k.val false with
  | false => simp only [hbit,hs,Bool.not_false,Bool.true_and]
  | true =>
      have hl := h k hs
      simp only [hl,Bool.not_true,Bool.false_eq_true] at hnot

theorem codePreparedCheck_of_dominance (q : ℕ) (p : PreparedValues) (x y : CostValues)
    (a b code : ℕ) (hb : 0< b) (h : CoefficientLe q x y a b)
    (hy : codePreparedCheck q p y b code=true) : codePreparedCheck q p x a code=true := by
  unfold codePreparedCheck at hy ⊢
  split at hy
  · rename_i hf
    rw [if_pos hf]
    apply List.all_eq_true.mpr
    intro e he
    exact decide_eq_true (preparedCost_bound_of_dominance q p x y a b hb h (codeRecord code) e
      (of_decide_eq_true (List.all_eq_true.mp hy e he)))
  · rename_i hf
    rw [if_neg hf]

theorem Tree.preparedCheck_of_dominance (small large : Array Bool) (hm : MaskLe small large)
    (q : ℕ) (pre : ℕ → PreparedValues) (x y : CostValues) (a b : ℕ)
    (hb : 0< b) (hc : CoefficientLe q x y a b) (t : Tree)
    (hy : t.preparedCheck large q pre y b=true) : t.preparedCheck small q pre x a=true := by
  induction t with
  | leaf bits key code =>
      by_cases hs : blocked small (Tree.leaf bits key code).mask=true
      · simp only [Tree.preparedCheck,hs,if_true]
      · have hl : blocked large (Tree.leaf bits key code).mask=false := by
          apply Bool.eq_false_iff.mpr
          exact fun hh => hs (blocked_of_maskLe small large hm _ hh)
        have hs' : blocked small (Tree.leaf bits key code).mask=false := Bool.eq_false_iff.mpr hs
        simp only [Tree.preparedCheck,hl,hs',Bool.false_eq_true,if_false] at hy ⊢
        exact codePreparedCheck_of_dominance q (pre key) x y a b code hb hc hy
  | branch bits pivot left right il ir =>
      by_cases hs : blocked small (Tree.branch bits pivot left right).mask=true
      · simp only [Tree.preparedCheck,hs,if_true]
      · have hl : blocked large (Tree.branch bits pivot left right).mask=false := by
          apply Bool.eq_false_iff.mpr
          exact fun hh => hs (blocked_of_maskLe small large hm _ hh)
        have hs' : blocked small (Tree.branch bits pivot left right).mask=false := Bool.eq_false_iff.mpr hs
        simp only [Tree.preparedCheck,hl,hs',Bool.false_eq_true,if_false] at hy ⊢
        obtain ⟨hleft,hright⟩ := and_true hy
        simp only [il hleft,ir hright,Bool.true_and]

end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (small large : Array.{0} Bool) (hm : Sensitivity213981Formal.ThreeBoundRankAnnotated.MaskLe small large) (q : Nat)
  (pre : Nat → Sensitivity213981Formal.ThreeBoundRankCached.PreparedValues)
  (x y : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (a b : Nat)
  (hb : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) b)
  (hc : Sensitivity213981Formal.ThreeBoundRankAnnotated.CoefficientLe q x y a b)
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (hy : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck large q pre y b t) Bool.true),
  @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck small q pre x a t) Bool.true := @Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree.preparedCheck_of_dominance
