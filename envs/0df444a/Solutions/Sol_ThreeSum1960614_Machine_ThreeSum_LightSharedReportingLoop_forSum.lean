-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop.forSum
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:51:39.544985+00:00
-- url     : https://prove2.me/submissions/980a42ce-8c46-4678-b1d0-75cc3d938b36

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
import Definitions.Def_ThreeSum1960614_Machine_Bundle032
import Definitions.Def_ThreeSum1960614_Machine_Bundle033
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSharedReportingLoop
end ThreeSum.LightSharedReportingLoop
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop.forSum__implementation_88e8736169 {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
    {σ : _root_.ThreeSum1960614.Machine.Light.State} {i : ℕ} {hi : _root_.ThreeSum1960614.Machine.Light.Expr} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (I : ℕ → _root_.ThreeSum1960614.Machine.Light.State → Prop) (n : ℕ) (b : ℕ → ℕ)
    (start : I 0 {σ with loc := Function.update σ.loc i 0})
    (round : ∀ (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State), j < n → σ.loc i=(j : ℤ) → I j σ →
      _root_.ThreeSum1960614.Machine.Light.Ends lim P d body σ (b j) (fun σ' =>
        σ'.loc i=(j : ℤ) ∧ I (j+1) {σ' with loc := Function.update σ'.loc i ((j : ℤ)+1)}))
    (done : ∀ (σ : _root_.ThreeSum1960614.Machine.Light.State), σ.loc i=(n : ℤ) → I n σ → Q σ)
    (bound : ∀ (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State), j ≤ n → σ.loc i=(j : ℤ) → I j σ →
      hi.Safe lim σ ∧ hi.val σ=(n : ℤ))
    (hn : (n : ℤ) ≤ lim.word)
    (hT : (∑ j ∈ Finset.range n, (hi.cost+b j+7))+hi.cost+5 ≤ T) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.for i hi body) σ T Q := by
  have h0 : (0 : ℤ) ≤ lim.word := (Int.natCast_nonneg n).trans hn
  refine _root_.ThreeSum1960614.Machine.Light.Ends.seq 2 ((∑ j ∈ Finset.range n, (hi.cost+b j+7))+hi.cost+3)
    (_root_.ThreeSum1960614.Machine.Light.Ends.set (by simpa using h0) (by simp) ?_) (by omega)
  have H := _root_.ThreeSum1960614.Machine.Light.Ends.while (lim := lim) (P := P) (d := d) (Q := Q)
    (σ := {σ with loc := Function.update σ.loc i 0})
    (c := (_root_.ThreeSum1960614.Machine.Light.Cond.lt (_root_.ThreeSum1960614.Machine.Light.v i) hi)) (s := (_root_.ThreeSum1960614.Machine.Light.Stmt.seq body (_root_.ThreeSum1960614.Machine.Light.Stmt.set i ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v i) (_root_.ThreeSum1960614.Machine.Light.k 1)))))
    (fun j σ => σ.loc i=(j : ℤ) ∧ I j σ) n (fun j => b j+4)
    (by exact ⟨by simp,by simpa using start⟩) ?round ?done
  · refine H.mono ?_ (fun _ h => h)
    simp only [_root_.ThreeSum1960614.Machine.Light.Cond.cost,_root_.ThreeSum1960614.Machine.Light.Expr.cost]
    have hsum : (∑ j ∈ Finset.range n, (1+hi.cost+1+1+(b j+4)))=
        ∑ j ∈ Finset.range n, (hi.cost+b j+7) := by
      apply Finset.sum_congr rfl
      intro j hj
      omega
    rw [hsum]
    omega
  case round =>
    rintro j σ hj ⟨hc,hI⟩
    obtain ⟨hs,hv⟩ := bound j σ hj.le hc hI
    refine ⟨⟨trivial,hs⟩,?_,_root_.ThreeSum1960614.Machine.Light.Ends.seq (b j) 4 ((round j σ hj hc hI).mono le_rfl ?_) le_rfl⟩
    · change σ.loc i < hi.val σ
      rw [hc,hv]
      exact_mod_cast hj
    · rintro σ' ⟨hc',hI'⟩
      have hval : (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v i) (_root_.ThreeSum1960614.Machine.Light.k 1))).val σ'=(j : ℤ)+1 := by simp [hc']
      have hj' : (j : ℤ)+1 ≤ n := by exact_mod_cast hj
      refine _root_.ThreeSum1960614.Machine.Light.Ends.set ⟨trivial,?_,?_⟩ (by simp) ⟨?_,?_⟩
      · change ((1 : ℕ) : ℤ) ≤ lim.word
        push_cast
        omega
      · change |(((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v i) (_root_.ThreeSum1960614.Machine.Light.k 1))).val σ'| ≤ lim.word
        rw [hval,abs_of_nonneg (by omega)]
        omega
      · simp [hc']
      · rw [hval]
        exact hI'
  case done =>
    rintro σ ⟨hc,hI⟩
    obtain ⟨hs,hv⟩ := bound n σ le_rfl hc hI
    refine ⟨⟨trivial,hs⟩,?_,done σ hc hI⟩
    change ¬ σ.loc i < hi.val σ
    rw [hc,hv]
    exact lt_irrefl _
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop.forSum__implementation_88e8736169) := (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingLoop.forSum__implementation_88e8736169)

#print axioms solution
