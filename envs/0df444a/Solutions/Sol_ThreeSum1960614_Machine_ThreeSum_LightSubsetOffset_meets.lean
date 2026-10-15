-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:21:48.567693+00:00
-- url     : https://prove2.me/submissions/09e6f0a2-e41e-4283-b21f-a2f720a885e2

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightSubsetOffset
end ThreeSum.LightSubsetOffset
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset
end ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetAddress


set_option maxRecDepth 4000

open _root_.Finset
open scoped _root_.BigOperators















































@[simp] theorem layerOffset_zero (L : ℕ) : _root_.ThreeSum.SubsetAddress.layerOffset L 0 = 0 := by
  simp [_root_.ThreeSum.SubsetAddress.layerOffset]

theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _









































































end ThreeSum.SubsetAddress

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Blocks -/











/-! ## The default proofs -/











/-! ## Rules for blocks -/













/-! ## Sequencing: what is left of the time goes to the rest of the program -/















/-- An assignment at the end of the program. -/
theorem Ends.setLast {loc μ : ℕ → ℤ} {T x : ℕ} {e : _root_.ThreeSum1960614.Machine.Light.Expr} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : Q ⟨Function.update loc x (e.val ⟨loc, μ⟩), μ⟩)
    (hs : e.Safe lim ⟨loc, μ⟩ := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                       (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                       simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT : e.cost + 1 ≤ T := by (first
                                                                            | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                first
                                                                                | omega
                                                                                | (ring_nf; omega))
                                                                            | omega
                                                                            |
                                                                              (simp [] <;>
                                                                                  first
                                                                                  | omega
                                                                                  | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.set x e) ⟨loc, μ⟩ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.set hs hT h













/-! ## Loops whose body is a block -/



/-! ## Counting loops -/







end Light

end

end ThreeSum1960614.Machine

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

namespace ThreeSum1960614.Machine

/-! # The layer-offset scan for compact downset addresses -/

namespace ThreeSum.LightSubsetOffset
open _root_.ThreeSum.LightSubsetOffset


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem layerOffset_bound (L k : ℕ) : _root_.ThreeSum.SubsetAddress.layerOffset L k ≤ k*2^L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
    have hb := Nat.choose_le_two_pow L k
    nlinarith







end ThreeSum.LightSubsetOffset

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSubsetOffset
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.meets__implementation_cf0286c800 {pOffset table W L k : ℕ}
    (hprog : P[pOffset]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : table+_root_.ThreeSum.LightPascal.tableSize W ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : _root_.ThreeSum.LightPascal.Table μ table W) (hL : L ≤ W) (hk : k ≤ W) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pOffset d [table,L,k,W] μ (_root_.ThreeSum.LightSubsetOffset.time k)
      (fun r μ' => r = (_root_.ThreeSum.SubsetAddress.layerOffset L k : ℤ) ∧ μ' = μ) := by
  have hsize : W+1 ≤ _root_.ThreeSum.LightPascal.tableSize W := by unfold _root_.ThreeSum.LightPascal.tableSize; nlinarith
  have hpow : (2^L : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hacc (i : ℕ) (hi : i ≤ k) :
      (_root_.ThreeSum.SubsetAddress.layerOffset L i : ℤ) ≤ lim.word := by
    have hm := Nat.mul_le_mul (show i ≤ W+1 by omega) hpow
    have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.layerOffset_bound L i).trans hm
    have hbZ : (_root_.ThreeSum.SubsetAddress.layerOffset L i : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ) := by
      exact_mod_cast hb
    exact hbZ.trans hword
  have hcast : (L : ℤ)*((W : ℤ)+1) = ((L*(W+1) : ℕ) : ℤ) := by push_cast; rfl
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hprog
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.body _root_.ThreeSum.LightSubsetOffset.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
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
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for (T := 30*k+6)
    (Q := fun σ => σ = ⟨_root_.Light.frame [table,L,k,W,k,(_root_.ThreeSum.SubsetAddress.layerOffset L k : ℕ)],μ⟩)
    (fun i σ => σ = ⟨_root_.Light.frame [table,L,k,W,i,(_root_.ThreeSum.SubsetAddress.layerOffset L i : ℕ)],μ⟩)
    k 22 ?_ ?_ ?_ ?_ (hT := by (first
                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                    first
                                    | omega
                                    | (ring_nf; omega))
                                | omega
                                |
                                  (simp [] <;>
                                      first
                                      | omega
                                      | (ring_nf; omega))))) ?_
  · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
  · rintro i _ hi _ rfl
    have hiW : i ≤ W := by omega
    have htRead := htable L hL i hiW
    have haddr : table+L*(W+1)+i < lim.space := by
      have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress.cell_offset_lt hL hiW
      omega
    have haddrEq : ((table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(i : ℤ)).toNat =
        table+L*(W+1)+i := by
      have he : (table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(i : ℤ) =
          ((table+L*(W+1)+i : ℕ) : ℤ) := by push_cast; rfl
      rw [he, Int.toNat_natCast]
    have htReadZ : μ (((table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(i : ℤ)).toNat) =
        (L.choose i : ℤ) := by rw [haddrEq, htRead]
    have hsum := hacc (i+1) (by omega)
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ, Nat.cast_add] at hsum
    have hnonneg : (0 : ℤ) ≤ (_root_.ThreeSum.SubsetAddress.layerOffset L i : ℤ) := Int.natCast_nonneg _
    have hcNonneg : (0 : ℤ) ≤ (L.choose i : ℤ) := Int.natCast_nonneg _
    refine _root_.ThreeSum1960614.Machine.Light.Ends.setLast ?_ (hs := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                                                                             (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                                                                             simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, htReadZ] <;> omega))) (hT := by (first
                                                                                                           | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                                               first
                                                                                                               | omega
                                                                                                               | (ring_nf; omega))
                                                                                                           | omega
                                                                                                           |
                                                                                                             (simp [] <;>
                                                                                                                 first
                                                                                                                 | omega
                                                                                                                 | (ring_nf; omega))))
    simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal, htReadZ, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  · intro σ hc hs
    exact hs
  · rintro i _ hi _ rfl
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
       (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
       simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  · intro σ hs
    rw [hs]
    have hf := hacc k le_rfl
    have hn : (0 : ℤ) ≤ (_root_.ThreeSum.SubsetAddress.layerOffset L k : ℤ) := Int.natCast_nonneg _
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.layerOffset L k : ℕ) ?_ ?_ ?_
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
    exact ⟨rfl,rfl⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.meets__implementation_cf0286c800) := (@ThreeSum1960614.Machine.ThreeSum.LightSubsetOffset.meets__implementation_cf0286c800)

#print axioms solution
