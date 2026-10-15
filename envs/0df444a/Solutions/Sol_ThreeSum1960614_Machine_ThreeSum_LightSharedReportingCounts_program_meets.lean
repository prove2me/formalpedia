-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:27:37.597045+00:00
-- url     : https://prove2.me/submissions/34ed2c5c-3495-42b7-abad-57a3cafbd6df

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle034
import Definitions.Def_ThreeSum1960614_Machine_Bundle035
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightPascal_build_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSharedReportingCounts
end ThreeSum.LightSharedReportingCounts
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts
end ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
end ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩









end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightSubsetAddress


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem cell_offset_lt {W i j : ℕ} (hi : i ≤ W) (hj : j ≤ W) :
    i*(W+1)+j < _root_.ThreeSum.LightPascal.tableSize W := by
  have hm := Nat.mul_le_mul_right (W+1) hi
  unfold _root_.ThreeSum.LightPascal.tableSize
  nlinarith











end ThreeSum.LightSubsetAddress

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout
set_option maxHeartbeats 1700000
set_option maxRecDepth 9000
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program_meets__implementation_ac9a41079e {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {μ : ℕ → ℤ} {h dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (horder : dst+2 ≤ work)
    (hconstants : (464 : ℤ) ≤ lim.word)
    (hspace : work+_root_.ThreeSum.LightPascal.tableSize (464*h) ≤ lim.space)
    (hpowWord : ((2^(464*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hcountWord : (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ) ≤ lim.word) (hd : d+464*h+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program 0 d [h,dst,work] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.time h)
      (fun r ν => r=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.SegN ν dst [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h] ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  have hh : h ≤ 464*h := by omega
  have h2h : 2*h ≤ 464*h := by omega
  have hstride : 464*h+1 ≤ _root_.ThreeSum.LightPascal.tableSize (464*h) := by unfold _root_.ThreeSum.LightPascal.tableSize; nlinarith
  have hL : 464*h ≤ lim.space := by omega
  have hlocal : _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h ≤ 2^(464*h+1) :=
    (Nat.choose_le_two_pow (464*h) h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hchoose2 : (464*h).choose (2*h) ≤ 2^(464*h+1) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hsplit : (2*h).choose h ≤ 2^(464*h+1) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 0) (by rfl : program[0]?=some (body 1))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.body _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (464 * h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.build_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program) (pBuild := 1) (pFill := 2) (pRow := 3) (pLinear := 4) (d := d + 1) (dst := work) (L := 464 * h) rfl rfl rfl rfl hw (by omega) hspace hpowWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightPascal.build_meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program) (pBuild := 1) (pFill := 2) (pRow := 3) (pLinear := 4) (d := d + 1) (dst := work) (L := 464 * h) rfl rfl rfl rfl hw (by omega) hspace hpowWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     on_goal -1 => (rintro result ν₁ ⟨htable, hkeepBuild⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hreadH := htable (464*h) le_rfl h hh
  have hreadE₁ := htable (464*h) le_rfl (2*h) h2h
  have hreadE₂ := htable (2*h) h2h h (by omega)
  have hcellH := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.cell_offset_lt (show 464*h ≤ 464*h from le_rfl) hh
  have hcellE₁ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.cell_offset_lt (show 464*h ≤ 464*h from le_rfl) h2h
  have hcellE₂ := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.cell_offset_lt h2h hh
  have hrowNZ : (0 : ℤ) ≤ 464*(h : ℤ)*(464*(h : ℤ)+1) := by positivity
  have hrowAddr : (work : ℤ)+464*(h : ℤ)*(464*(h : ℤ)+1)+2*(h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work+464*h*(464*h+1)+2*h < lim.space by omega)
  have hgroupNZ : (0 : ℤ) ≤ 2*(h : ℤ)*(464*(h : ℤ)+1) := by positivity
  have hgroupAddr : (work : ℤ)+2*(h : ℤ)*(464*(h : ℤ)+1)+(h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work+2*h*(464*h+1)+h < lim.space by omega)
  have hprod : ((464*h).choose (2*h) : ℤ)*((2*h).choose h : ℤ)=(_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ) := by
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs,_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth,_root_.ThreeSum.LightReportingPrefixArrays.localCount,Nat.cast_mul]
  have hprodNZ : (0 : ℤ) ≤ ((464*h).choose (2*h) : ℤ)*((2*h).choose h : ℤ) := by positivity
  have haH : ((work : ℤ)+(464*(h : ℤ))*(464*(h : ℤ)+1)+(h : ℤ)).toNat=
      work+(464*h)*(464*h+1)+h := by
    have he : (work : ℤ)+(464*(h : ℤ))*(464*(h : ℤ)+1)+(h : ℤ)=
        ((work+(464*h)*(464*h+1)+h : ℕ) : ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  have haE₁ : ((work : ℤ)+(464*(h : ℤ))*(464*(h : ℤ)+1)+2*(h : ℤ)).toNat=
      work+(464*h)*(464*h+1)+2*h := by
    have he : (work : ℤ)+(464*(h : ℤ))*(464*(h : ℤ)+1)+2*(h : ℤ)=
        ((work+(464*h)*(464*h+1)+2*h : ℕ) : ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  have haE₂ : ((work : ℤ)+2*(h : ℤ)*(464*(h : ℤ)+1)+(h : ℤ)).toNat=
      work+2*h*(464*h+1)+h := by
    have he : (work : ℤ)+2*(h : ℤ)*(464*(h : ℤ)+1)+(h : ℤ)=
        ((work+2*h*(464*h+1)+h : ℕ) : ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadH, haH, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadH, haH, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadH, haH, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((464 * h).choose (2 * h) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadE₁, haE₁, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadE₁, haE₁, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadE₁, haE₁, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((2 * h).choose h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadE₂, haE₂, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hreadE₂, haE₂, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadE₂, haE₂, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightReportingPrefixArrays.localCount, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightReportingPrefixArrays.localCount, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs, _root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localWidth, _root_.ThreeSum.LightReportingPrefixArrays.localCount, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPascal.buildTime, _root_.ThreeSum.LightPascal.rowTime, _root_.ThreeSum.LightArray.linearTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp,?_,?_⟩
  · intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> simp [_root_.ThreeSum1960614.Machine.Light.SegN]
  · intro a ha
    change Function.update (Function.update ν₁ dst (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localChoose h : ℤ)) (dst+1) (_root_.ThreeSum1960614.Machine.ThreeSum.SharedReportingBankLayout.localPairs h : ℤ) a=μ a
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeepBuild a (Or.inl (by omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program_meets__implementation_ac9a41079e) := (@ThreeSum1960614.Machine.ThreeSum.LightSharedReportingCounts.program_meets__implementation_ac9a41079e)

#print axioms solution
