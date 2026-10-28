-- Prove2me | solution 1 for Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.cachedCheck_sound
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-27T00:40:29.728258+00:00
-- url     : https://prove2.me/submissions/9f76b611-dd38-4d07-91b8-3d6f7484fdf8

import Definitions.Def_Sensitivity213981Formal_Namespaces
import Definitions.Def_Sensitivity213981Formal_NamespacesComplete
import Definitions.Def_Sensitivity213981Formal_RankAnnotatedTree
import Definitions.Def_Sensitivity213981Formal_RankPackedVariableCache
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
/- Reuse a certified variable-cost maximum across all rows with the same
packed capcode and external count.  Lookups verify both arguments exactly.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace ThreeBoundEndpoint22Packed
open ThreeBoundNumeric (maximum)
open ThreeBoundRankCached ThreeBoundRankAnnotated
open ThreeBoundEndpoint22Records









theorem VariableCache.lookup_sound (q : ℕ) (values : CostValues) (cache : VariableCache)
    (hc : cache.check q values=true) (capcode external value : ℕ)
    (hl : cache.lookup capcode external=some value) :
    variableMaximum q capcode values external≤ value := by
  induction cache with
  | leaf code ext v =>
      simp only [VariableCache.lookup] at hl
      split at hl
      · rename_i he
        obtain ⟨rfl,rfl⟩:=he
        have hv : v=value := Option.some.inj hl
        subst value
        exact of_decide_eq_true hc
      · contradiction
  | branch pivot left right il ir =>
      obtain ⟨hleft,hright⟩:=and_true hc
      simp only [VariableCache.lookup] at hl
      split at hl
      · exact il hleft hl
      · exact ir hright hl





theorem cachedCodeCheck_sound (q : ℕ) (cache : VariableCache) (capcode : ℕ)
    (values : CostValues) (bound code : ℕ) (hc : cache.check q values=true)
    (h : cachedCodeCheck cache capcode values bound code=true) :
    packedCodeCheck q capcode values bound code=true := by
  cases hl : cache.lookup capcode (codeRecord code 11) with
  | none => simp only [cachedCodeCheck,hl,Bool.false_eq_true] at h
  | some v =>
      have hv := cache.lookup_sound q values hc capcode (codeRecord code 11) v hl
      have hb : headSum values (codeRecord code)+v≤ bound := by
        exact of_decide_eq_true (by simpa only [cachedCodeCheck,hl] using h)
      apply decide_eq_true
      exact (Nat.add_le_add_left hv _).trans hb



theorem Tree.cachedCheck_sound (deny q : ℕ) (cache : VariableCache) (values : CostValues)
    (bound : ℕ) (hc : cache.check q values=true) (t : ThreeBoundRankAnnotated.Tree)
    (h : Tree.cachedCheck deny cache values bound t=true) :
    Tree.fastCheck deny q values bound t=true := by
  induction t with
  | leaf bits key code =>
      simp only [Tree.cachedCheck,Tree.fastCheck] at h ⊢
      split at h
      · rename_i hb
        simp only [hb,if_true]
      · rename_i hb
        simp only [hb,if_false]
        exact cachedCodeCheck_sound q cache (convertedCodes.get key) values bound code hc h
  | branch bits pivot left right il ir =>
      simp only [Tree.cachedCheck,Tree.fastCheck] at h ⊢
      split at h
      · rename_i hb
        simp only [hb,if_true]
      · rename_i hb
        simp only [hb,if_false]
        obtain ⟨hl,hr⟩:=and_true h
        simp only [il hl,ir hr,Bool.true_and,Bool.false_eq_true,if_false]





end ThreeBoundEndpoint22Packed



end
end Sensitivity213981Formal

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 200000
theorem solution :
∀ (deny q : Nat) (cache : Sensitivity213981Formal.ThreeBoundEndpoint22Packed.VariableCache)
  (values : Sensitivity213981Formal.ThreeBoundRankCached.CostValues) (bound : Nat)
  (hc : @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.VariableCache.check q values cache) Bool.true)
  (t : Sensitivity213981Formal.ThreeBoundRankAnnotated.Tree)
  (h :
    @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.cachedCheck deny cache values bound t)
      Bool.true),
  @Eq.{1} Bool (Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.fastCheck deny q values bound t) Bool.true := @Sensitivity213981Formal.ThreeBoundEndpoint22Packed.Tree.cachedCheck_sound
