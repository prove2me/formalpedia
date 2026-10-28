-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck_eq
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-26T20:53:56.678629+00:00
-- url     : https://prove2.me/submissions/0c5701bf-d708-4da1-a754-68ce33c89f1c

import Definitions.Def_Sensitivity213981Formal_Endpoint22FusedPrepared
import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
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


















theorem le_maximum_of_mem {xs : List ℕ} {x : ℕ} (h : x ∈ xs) :
    x ≤  maximum xs := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact le_max_left _ _
      · exact (ih h).trans (le_max_right _ _)

theorem maximum_le {xs : List ℕ} {k : ℕ} (h : ∀ x ∈ xs, x ≤  k) :
    maximum xs ≤  k := by
  induction xs with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
      exact max_le (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))





















end ThreeBoundNumeric



end
end Sensitivity213981Formal

namespace Sensitivity213981Formal
section
/- Evaluate the head sum once, outside the finite external-count maximum. -/


set_option autoImplicit false
set_option maxHeartbeats 500000
namespace ThreeBoundRankAnnotated
open ThreeBoundNumeric (maximum maximum_le le_maximum_of_mem)
open ThreeBoundRankCached ThreeBoundRankNumeric
open ThreeBoundEndpoint22Records



theorem preparedCost_split (q : ℕ) (p : PreparedValues) (values : CostValues)
    (r : Record) (e : ℕ) : preparedCost q p values r e =
      variablePreparedCost q p values (r 11) e + headSum values r := rfl



/-- The fused checker is exactly equivalent to checking every external count. -/
theorem fusedCodePreparedCheck_eq (q : ℕ) (p : PreparedValues) (values : CostValues)
    (bound code : ℕ) : fusedCodePreparedCheck q p values bound code =
      codePreparedCheck q p values bound code := by
  unfold fusedCodePreparedCheck codePreparedCheck
  split_ifs with hf
  · dsimp only
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, decide_eq_true_eq, preparedCost_split]
    constructor
    · intro h e he
      have hc : variablePreparedCost q p values (codeRecord code 11) e ≤ 
          maximum ((List.range (codeRecord code 11+1)).map
            fun e => variablePreparedCost q p values (codeRecord code 11) e) :=
        le_maximum_of_mem (List.mem_map.mpr ⟨e,he,rfl⟩)
      apply decide_eq_true_eq.mpr
      omega
    · intro h
      have h0 := of_decide_eq_true (h 0 (by simp))
      have hhead : headSum values (codeRecord code) ≤  bound := by omega
      have hmax : maximum ((List.range (codeRecord code 11+1)).map
          fun e => variablePreparedCost q p values (codeRecord code 11) e) ≤ 
          bound-headSum values (codeRecord code) := by
        apply maximum_le
        intro value hv
        obtain ⟨e,he,rfl⟩ := List.mem_map.mp hv
        exact (Nat.le_sub_iff_add_le hhead).mpr (of_decide_eq_true (h e he))
      omega
  · rfl

end ThreeBoundRankAnnotated


end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (q : Nat) (p : Sensitivity213981Formal.ThreeBoundRankCached.PreparedValues)
  (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound code : Nat),
  @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck q p values bound code)
    (Sensitivity213981Formal.ThreeBoundRankAnnotated.codePreparedCheck q p values bound code) := @Sensitivity213981Formal.ThreeBoundRankAnnotated.fusedCodePreparedCheck_eq
