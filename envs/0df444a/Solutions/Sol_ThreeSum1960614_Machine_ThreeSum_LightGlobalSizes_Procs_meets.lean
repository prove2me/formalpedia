-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:01:24.311017+00:00
-- url     : https://prove2.me/submissions/cf7aed30-bc7f-4a0f-88f2-7d282bc1d19e

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_Light_sqrt_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNatPower_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets

private theorem platform_seg_cons_88b5e7f1ff {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

@[simp] private theorem platform_seg_nil_88b5e7f1ff (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightGlobalSizes
end ThreeSum.LightGlobalSizes
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
end ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)





































































end Light

end

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightGlobalSizes
open _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes

set_option maxHeartbeats 1000000
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.Procs.meets__implementation_31ec154eff {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.Procs P pMain)
    {μ : ℕ → ℤ} {C p J mu dst : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hC : 1 ≤ C) (hp : 1 ≤ p) (hspace : dst+5 ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word C p J mu : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [C,p,J,mu,dst] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.time C J mu)
      (fun r μ' => r = ((p^J : ℕ) : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values C p J mu) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst 5) := by
  have hMpos : 0 < C^J := Nat.pow_pos (by omega)
  have hRpos : 0 < p^J := Nat.pow_pos (by omega)
  have hDpos : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu := Nat.two_pow_pos _
  have hroot : _root_.ThreeSum.LightGlobalSizes.root C J ≤ C^J+1 := by
    unfold _root_.ThreeSum.LightGlobalSizes.root _root_.ThreeSum.LocalCoverBounds.rootCeiling
    have hs := Nat.sqrt_le_self (C^J-1)
    omega
  have hrootPos : 0 < _root_.ThreeSum.LightGlobalSizes.root C J := _root_.ThreeSum.LocalCoverBounds.rootCeiling_pos _
  have heLe : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent mu ≤ mu := by
    have h := Nat.div_mul_le_self (62656016*mu) 1000000000
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent
    omega
  have hnum : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu ≤ C^J+_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu+1 := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator; omega
  have hband : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.band C J mu ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu := Nat.div_le_self _ _
  have hbound (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word C p J mu) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hconst : (1000000000 : ℤ) ≤ lim.word := hbound 1000000000 (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hnumMuWord : (62656016 : ℤ)*(mu : ℤ) ≤ lim.word := by
    simpa using hbound (62656016*mu) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hCw := hbound C (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hpw := hbound p (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hJw := hbound J (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hmuw := hbound mu (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hMw := hbound (C^J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hRw := hbound (p^J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hMZpos : (0 : ℤ) < (C : ℤ)^J := by exact_mod_cast hMpos
  have hMZw : (C : ℤ)^J ≤ lim.word := by exact_mod_cast hMw
  have hRZpos : (0 : ℤ) < (p : ℤ)^J := by exact_mod_cast hRpos
  have hRZw : (p : ℤ)^J ≤ lim.word := by exact_mod_cast hRw
  have hDw := hbound (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hrw := hbound (_root_.ThreeSum.LightGlobalSizes.root C J) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hnw := hbound (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hsumw := hbound (_root_.ThreeSum.LightGlobalSizes.root C J+_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hsumZw : (_root_.ThreeSum.LightGlobalSizes.root C J : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu : ℤ) ≤ lim.word := by exact_mod_cast hsumw
  have hbw := hbound (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.band C J mu) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hew := hbound (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent mu) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have heZ : (0 : ℤ) ≤ (62656016*(mu : ℤ))/1000000000 := by positivity
  have heZw : (62656016*(mu : ℤ))/1000000000 ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using hew
  have hpowC (i : ℕ) (hi : i ≤ J) : ((C^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hC hi)).trans hMw
  have hpowP (i : ℕ) (hi : i ≤ J) : ((p^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hp hi)).trans hRw
  have hpowD (i : ℕ) (hi : i ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent mu) : ((2^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hDw
  have hsub : ((C^J : ℕ) : ℤ)-1 = ((C^J-1 : ℕ) : ℤ) := by omega
  have hnumEq : (_root_.ThreeSum.LightGlobalSizes.root C J : ℤ)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu : ℤ)-1 = (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu : ℤ) := by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.body _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) S.power μ hJw hpowC) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) S.power μ hJw hpowC) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro mval μ₁ ⟨hmval, hmem₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₁
  have hmvalZ : mval = (C : ℤ)^J := by simpa only [Nat.cast_pow] using hmval
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) S.power μ hJw hpowP) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) S.power μ hJw hpowP) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro rval μ₂ ⟨hrval, hmem₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  have hrvalZ : rval = (p : ℤ)^J := by simpa only [Nat.cast_pow] using hrval
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := 62656016 * mu) (b := 1000000000) S.divide μ (hbound _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega))) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := 62656016 * mu) (b := 1000000000) S.divide μ (hbound _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega))) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro e μ₃ ⟨he, hmem₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₃
  have heInt : e=(62656016*(mu : ℤ))/1000000000 := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using he
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) S.power μ hew hpowD) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) S.power μ hew hpowD) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, heInt, _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [heInt, _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, heInt, _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro dval μ₄ ⟨hdval, hmem₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₄
  have hdval' : dval = (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu : ℤ) := hdval
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.sqrt_meets (d := d + 1) (K := C ^ J - 1) S.sqrt μ (hbound _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega))) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.sqrt_meets (d := d + 1) (K := C ^ J - 1) S.sqrt μ (hbound _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega))) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmvalZ, hsub, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hmvalZ, hsub, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmvalZ, hsub, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro s μ₅ ⟨hs, hmem₅⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₅
  have hs' : s+1 = (_root_.ThreeSum.LightGlobalSizes.root C J : ℤ) := by
    simpa [_root_.ThreeSum.LightGlobalSizes.root,_root_.ThreeSum.LocalCoverBounds.rootCeiling] using congrArg (fun z : ℤ => z+1) hs
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightGlobalSizes.root C J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hs', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hs', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hs', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdval', hnumEq, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hdval', hnumEq, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdval', hnumEq, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu) (b := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu) S.divide μ (hbound _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega))) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator C J mu) (b := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu) S.divide μ (hbound _ (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega))) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hdval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro bval μ₆ ⟨hbval, hmem₆⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₆
  have hbval' : bval = (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.band C J mu : ℤ) := hbval
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (C ^ J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hmvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hmvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hmvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (p ^ J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 2) (_root_.ThreeSum.LightGlobalSizes.root C J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 3) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor mu : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hdval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 4) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.band C J mu : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbval', _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (p ^ J : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrvalZ, _root_.ThreeSum.LightNatPower.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  exact ⟨rfl,by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values,platform_seg_cons_88b5e7f1ff],by 
      (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
         intro p2m_macro_8066091321798120387 p2m_macro_10895178223973276270
         first
         | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_15219926541250029525); (try have := p2m_macro_15219926541250029525 p2m_macro_8066091321798120387 (by omega)); revert p2m_macro_15219926541250029525)
               intros
               try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
         |
           (simp [] at p2m_macro_10895178223973276270;
             ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_6743074454999559703); (try have := p2m_macro_6743074454999559703 p2m_macro_8066091321798120387 (by omega)); revert p2m_macro_6743074454999559703)
               intros
               try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
         | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_6630565688069677297); (try have := p2m_macro_6630565688069677297 p2m_macro_8066091321798120387 (by omega)); revert p2m_macro_6630565688069677297)
               intros
               try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
             fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                         SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                         its condition K x does not follow from the hypotheses.")))⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.Procs.meets__implementation_31ec154eff) := (@ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.Procs.meets__implementation_31ec154eff)

#print axioms solution
