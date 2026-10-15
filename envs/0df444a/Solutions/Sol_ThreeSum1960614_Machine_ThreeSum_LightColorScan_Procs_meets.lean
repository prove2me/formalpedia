-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightColorScan.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:02:03.89317+00:00
-- url     : https://prove2.me/submissions/d6cd2098-5c94-42be-8a57-410f567be04e

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
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
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
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightColorParameters_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ColorParameters
end ThreeSum.ColorParameters
namespace ThreeSum.ColorScan
end ThreeSum.ColorScan
namespace ThreeSum.LightColorScan
end ThreeSum.LightColorScan
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ColorParameters
end ThreeSum1960614.Machine.ThreeSum.ColorParameters
namespace ThreeSum1960614.Machine.ThreeSum.ColorScan
end ThreeSum1960614.Machine.ThreeSum.ColorScan
namespace ThreeSum1960614.Machine.ThreeSum.LightColorScan
end ThreeSum1960614.Machine.ThreeSum.LightColorScan

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
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl









/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}















/-! ## The tactics -/











end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A literal small coloring-parameter order

There are exactly 81*W² integer slots. Four ternary digits select the
color map, and the remaining quotient selects its two binary coordinates.
The inverse code proves that every separating parameter is present.
-/

namespace ThreeSum.ColorParameters
open _root_.ThreeSum.ColorParameters
















theorem fields_parameter {W t : ℕ} (ht : t < _root_.ThreeSum.ColorParameters.count W) : _root_.ThreeSum.ColorParameters.fields (_root_.ThreeSum.ColorParameters.parameter ht)=_root_.ThreeSum.ColorParameters.data W t := rfl















end ThreeSum.ColorParameters

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Correctness of a prefix of the literal coloring family -/

namespace ThreeSum.ColorScan
open _root_.ThreeSum.ColorScan


open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters



theorem hit_zero {n W : ℕ} (x : Fin n → ℤ) : ¬ _root_.ThreeSum.ColorScan.Hit x W 0 := by
  rintro ⟨i,hi,hlt,_⟩
  omega

theorem hit_mono {n W a b : ℕ} {x : Fin n → ℤ} (hab : a ≤ b) :
    _root_.ThreeSum.ColorScan.Hit x W a → _root_.ThreeSum.ColorScan.Hit x W b := by
  rintro ⟨i,hi,hlt,hx⟩
  exact ⟨i,hi,hlt.trans_le hab,hx⟩

theorem hit_succ {n W t : ℕ} (x : Fin n → ℤ) (ht : t < _root_.ThreeSum.ColorParameters.count W) :
    _root_.ThreeSum.ColorScan.Hit x W (t+1) ↔ _root_.ThreeSum.ColorScan.Hit x W t ∨ _root_.ThreeSum.ColorClassLists.witness (_root_.ThreeSum.ColorParameters.parameter ht) x := by
  constructor
  · rintro ⟨i,hi,hlt,hx⟩
    by_cases he : i=t
    · subst i
      exact Or.inr hx
    · exact Or.inl ⟨i,hi,by omega,hx⟩
  · rintro (⟨i,hi,hlt,hx⟩ | hx)
    · exact ⟨i,hi,by omega,hx⟩
    · exact ⟨t,ht,by omega,hx⟩



end ThreeSum.ColorScan

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightColorScan
open _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScan

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.ColorParameters
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters
open _root_.ThreeSum.ColorScan
open _root_.ThreeSum1960614.Machine.ThreeSum.ColorScan
set_option maxHeartbeats 2200000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightColorScan.Procs.meets__implementation_3b33178ac1 {pMain src n params free W colorTime colorDepth : ℕ}
    (R : _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScan.Procs P pMain) (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : free+6 ≤ lim.space) (hsrc : src ≤ free) (hparams : params ≤ free)
    (hword : ((n+_root_.ThreeSum.ColorParameters.count W+W+100 : ℕ) : ℤ) ≤ lim.word)
    (hcolor : ∀ (i : ℕ) (hi : i < _root_.ThreeSum.ColorParameters.count W) (ν : ℕ → ℤ),
      _root_.ThreeSum1960614.Machine.Light.Kept μ ν free → _root_.ThreeSum1960614.Machine.Light.Seg ν free (_root_.ThreeSum.ColorParameters.fields (_root_.ThreeSum.ColorParameters.parameter hi)) →
      ∀ dd : ℕ, dd+colorDepth ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P R.pColor dd [src,n,params,free,free+6] ν colorTime
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ _root_.ThreeSum.ColorClassLists.witness (_root_.ThreeSum.ColorParameters.parameter hi) x) ∧ _root_.ThreeSum1960614.Machine.Light.Kept ν ξ free))
    {t d : ℕ} {ν : ℕ → ℤ} (ht : t ≤ _root_.ThreeSum.ColorParameters.count W)
    (hd : d+t+colorDepth+3 ≤ lim.depth) (hkeep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [src,n,params,free,W,t] ν (_root_.ThreeSum.LightColorScan.time colorTime W t)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ _root_.ThreeSum.ColorScan.Hit x W t) ∧ _root_.ThreeSum1960614.Machine.Light.Kept ν ξ free) := by
  have hsmall (a : ℕ) (ha : a ≤ n+_root_.ThreeSum.ColorParameters.count W+W+100) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have htwo := hsmall 2 (by omega)
  have hW := hsmall W (by omega)
  have hcount := hsmall (_root_.ThreeSum.ColorParameters.count W) (by omega)
  have hn := hsmall n (by omega)
  induction t generalizing d ν with
  | zero =>
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScan.body _root_.ThreeSum.LightColorScan.time
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < 0) (fun hbad => ?_) (fun hno => ?_) ?_ ?_
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
         all_goals
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
      · omega
      · (focus
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
        exact ⟨by simp,by simp [_root_.ThreeSum1960614.Machine.ThreeSum.ColorScan.hit_zero],_root_.ThreeSum1960614.Machine.Light.SameOn.refl⟩
  | succ t ih =>
      have ht' : t < _root_.ThreeSum.ColorParameters.count W := by omega
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body R.main
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightColorScan.body _root_.ThreeSum.LightColorScan.time
      (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < ((t + 1 : ℕ) : ℤ)) (fun hyes => ?_) (fun hbad => ?_) ?_ ?_
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
         all_goals
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
      · have hrec := ih (d := d+1) (ν := ν) (by omega) (by omega) hkeep
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
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrec _ (by omega)) ?_ ?_ ?_ ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrec ?_ ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum.LightColorScan.time] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time] <;> omega)
           on_goal -1 => (rintro prev ν₁ ⟨hprevBool, hprev, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        have hprevRange : 0 ≤ prev ∧ prev ≤ 1 := by rcases hprevBool with hh | hh <;> omega
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen ((0 : ℤ) < prev) (fun hhit => ?_) (fun hmiss => ?_) ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum.LightColorScan.time] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time] <;> omega)
           all_goals
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
        · have hh := _root_.ThreeSum1960614.Machine.ThreeSum.ColorScan.hit_mono (by omega : t ≤ t+1) (hprev.mp (by omega))
          (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (1 : ℕ) ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightColorScan.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time] <;> omega)
             try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
          exact ⟨by simp,by simpa using hh,hkeep₁⟩
        · have hnoHit : ¬ _root_.ThreeSum.ColorScan.Hit x W t := fun hh => hmiss (by have := hprev.mpr hh; omega)
          (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (t : ℕ) ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightColorScan.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time] <;> omega)
             try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
          have hp := _root_.ThreeSum1960614.Machine.ThreeSum.LightColorParameters.meets (d := d+1) (W := W) (t := t) (free := free)
            (μ := ν₁) R.parameters R.divide hw hspace (hsmall _ (by omega)) (by omega)
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
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hp _ (by omega)) ?_ ?_ ?_ ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hp ?_ ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 => omega
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time] <;> omega)
             on_goal -1 => (rintro row ν₂ ⟨hrow, hdata, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
          have hrowData : _root_.ThreeSum1960614.Machine.Light.Seg ν₂ free (_root_.ThreeSum.ColorParameters.fields (_root_.ThreeSum.ColorParameters.parameter ht')) := by
            simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ColorParameters.fields_parameter] using hdata
          have hkeepBefore : _root_.ThreeSum1960614.Machine.Light.Kept ν₁ ν₂ free := fun i hi => hkeep₂ i (Or.inl hi)
          have htotal : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₂ free := fun i hi =>
            (hkeepBefore i hi).trans ((hkeep₁ i hi).trans (hkeep i hi))
          have hc := hcolor t ht' ν₂ htotal hrowData (d+1) (by omega)
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
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 => omega
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time] <;> omega)
             on_goal -1 => (rintro result ξ ⟨hbool, hresult, hkeep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
          have hrange : 0 ≤ result ∧ result ≤ 1 := by rcases hbool with hh | hh <;> omega
          (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen result ?_ ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightColorScan.time, _root_.ThreeSum.LightColorParameters.time] <;> omega)
             try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
          refine ⟨hbool,?_,?_⟩
          · rw [_root_.ThreeSum1960614.Machine.ThreeSum.ColorScan.hit_succ x ht',or_iff_right hnoHit]
            exact hresult
          · intro i hi
            exact (hkeep₃ i hi).trans ((hkeepBefore i hi).trans (hkeep₁ i hi))
      · omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightColorScan.Procs.meets__implementation_3b33178ac1) := (@ThreeSum1960614.Machine.ThreeSum.LightColorScan.Procs.meets__implementation_3b33178ac1)

#print axioms solution
