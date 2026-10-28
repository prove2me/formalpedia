-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankCached.rankA_le_of_bounds
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:27:55.643861+00:00
-- url     : https://prove2.me/submissions/d3f96942-51ac-44dc-a37a-caf74b0eada5

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankCachedEvaluator
import Definitions.Def_Sensitivity213981Formal_Supplement_NumericExpressions
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
/- Homogeneous arithmetic expressions for the exact sensitivity transfer.
Every operation is interpreted in Nat. In particular subtraction is truncated
subtraction, which commutes with multiplication by every natural scalar. -/


set_option autoImplicit false

namespace ThreeBoundNumeric
open ThreeBoundFullProfile
















@[simp] theorem maximum_cons (x : ℕ) (xs : List ℕ) :
    maximum (x::xs) = max x (maximum xs) := rfl



theorem maximum_le {xs : List ℕ} {k : ℕ} (h : ∀ x ∈ xs, x ≤  k) :
    maximum xs ≤  k := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

theorem Expr.eval_maximum {n : ℕ} (es : List (Expr n)) (v : Profile n) :
    (Expr.maximum es).eval v = ThreeBoundNumeric.maximum (es.map (fun e => e.eval v)) := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa only [Expr.maximum, List.foldr_cons, Expr.eval,
      List.map_cons, maximum_cons] using congrArg (Nat.max (e.eval v)) ih



















end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Exact coefficient caching and filtered-tree bounds for the q3 rank transfer. -/


set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace ThreeBoundRankCached
open ThreeBoundNumeric (Caps Expr aExpr bExpr recordOfList   maximum maximum_le)
open ThreeBoundFullProfile ThreeBoundRankNumeric
open scoped BigOperators



















































theorem rankA_le_of_bounds (n : ℕ) (v : Profile n) (caps : Caps) (perfect : ℕ)
    (records : List (List ℕ)) (a c : Entry) (bound : ℕ)
    (h : ∀ xs∈records, recordAllowed n caps a c (recordOfList xs)=true →
      ∀ e≤ recordOfList xs 11, (recordCost n caps perfect a c (recordOfList xs) e).eval v≤ bound) :
    (rankAExpr n caps perfect records a c).eval v≤ bound := by
  rw [rankAExpr,Expr.eval_maximum]
  apply maximum_le
  intro value hv
  obtain ⟨expr,hexpr,rfl⟩ := List.mem_map.mp hv
  obtain ⟨xs,hxs,hexpr⟩ := List.mem_flatMap.mp hexpr
  by_cases ha : recordAllowed n caps a c (recordOfList xs)=true
  · rw [if_pos ha] at hexpr
    obtain ⟨e,he,rfl⟩ := List.mem_map.mp hexpr
    exact h xs hxs ha e (by have hh := List.mem_range.mp he; omega)
  · rw [if_neg ha] at hexpr
    contradiction





end ThreeBoundRankCached




end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (n : Nat) (v : Sensitivity213981Formal.ThreeBoundFullProfile.Profile n)
  (caps : Sensitivity213981Formal.ThreeBoundNumeric.Caps) (perfect : Nat) (records : List.{0} (List.{0} Nat))
  (a c : Sensitivity213981Formal.ThreeBoundRankNumeric.Entry) (bound : Nat)
  (h :
    ∀ (xs : List.{0} Nat),
      @Membership.mem.{0, 0} (List.{0} Nat) (List.{0} (List.{0} Nat)) (@List.instMembership.{0} (List.{0} Nat)) records
          xs →
        @Eq.{1} Bool
            (Sensitivity213981Formal.ThreeBoundRankNumeric.recordAllowed n caps a c
              (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs))
            Bool.true →
          ∀ (e : Nat),
            @LE.le.{0} Nat instLENat e
                (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs
                  (@OfNat.ofNat.{0} Nat (nat_lit 11) (instOfNatNat (nat_lit 11)))) →
              @LE.le.{0} Nat instLENat
                (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
                  (Sensitivity213981Formal.ThreeBoundRankNumeric.recordCost n caps perfect a c
                    (Sensitivity213981Formal.ThreeBoundNumeric.recordOfList xs) e))
                bound),
  @LE.le.{0} Nat instLENat
    (@Sensitivity213981Formal.ThreeBoundNumeric.Expr.eval n v
      (Sensitivity213981Formal.ThreeBoundRankNumeric.rankAExpr n caps perfect records a c))
    bound := @Sensitivity213981Formal.ThreeBoundRankCached.rankA_le_of_bounds
