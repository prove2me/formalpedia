-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:27:32.730509+00:00
-- url     : https://prove2.me/submissions/f1d52ea3-b8b0-4d94-8a3f-19d38708b758

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_PaperStatements
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_WordSize
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
import Definitions.Def_ThreeSum1960614_Machine_Bundle002
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
import Definitions.Def_TrulySubcubicAPSP_SourceSpecification
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
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
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Combinatorics.SimpleGraph.Basic
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
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.LightEncodedColorLayout
end ThreeSum.LightEncodedColorLayout
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandPartition
end ThreeSum1960614.Machine.ThreeSum.BandPartition
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout
end ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout

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

/-! # Compute and retain the selected-color array layout -/

namespace ThreeSum.LightEncodedColorLayout
open _root_.ThreeSum.LightEncodedColorLayout


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 11000








theorem headMemory_kept (μ : ℕ → ℤ) (free n g : ℕ) : _root_.ThreeSum1960614.Machine.Light.Kept μ (_root_.ThreeSum.LightEncodedColorLayout.headMemory μ free n g) free := by
  intro q hq
  unfold _root_.ThreeSum.LightEncodedColorLayout.headMemory
  repeat rw [Function.update_of_ne (by omega)]

theorem headMemory_heads (μ : ℕ → ℤ) (free n g : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg (_root_.ThreeSum.LightEncodedColorLayout.headMemory μ free n g) free (_root_.ThreeSum.EncodedColorLayout.normalizedHeads free n g) := by
  intro i hi
  have hi' : i < 8 := by simpa [_root_.ThreeSum.EncodedColorLayout.normalizedHeads] using hi
  interval_cases i <;> simp [_root_.ThreeSum.LightEncodedColorLayout.headMemory,_root_.ThreeSum.EncodedColorLayout.normalizedHeads]

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightEncodedColorLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightEncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.BandPartition
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPartition
open _root_.ThreeSum.EncodedColorLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorLayout
set_option maxHeartbeats 2200000
set_option maxRecDepth 11000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.meets__implementation_bf583d8cf2 {pMain pDivide n g free : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.body pDivide)) (hdiv : P[pDivide]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hg : 0 < g)
    (hspace : _root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g+1 ≤ lim.space)
    (hword : (_root_.ThreeSum.LightEncodedColorLayout.word n g : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [n,g,free] μ (_root_.ThreeSum.LightEncodedColorLayout.time n g)
      (fun r ν => r=(_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg ν free (_root_.ThreeSum.EncodedColorLayout.normalizedHeads free n g) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  have hfull : free+17+13*n+5*_root_.ThreeSum.ColorBandBounds.count n g+3*g*_root_.ThreeSum.ColorBandBounds.count n g+1 ≤ lim.space := by
    convert hspace using 1 <;>
      simp only [_root_.ThreeSum.EncodedColorLayout.normalizedEnd,_root_.ThreeSum.LightBandRawA.space,_root_.ThreeSum.LightBandRawA.positionBase,_root_.ThreeSum.LightBandRawA.ownerBase,
        _root_.ThreeSum.LightBandRawA.capacity,_root_.ThreeSum.EncodedColorLayout.vals,_root_.ThreeSum.EncodedColorLayout.rec,_root_.ThreeSum.EncodedColorLayout.tables,_root_.ThreeSum.EncodedColorLayout.ce,_root_.ThreeSum.EncodedColorLayout.cv,_root_.ThreeSum.EncodedColorLayout.be,_root_.ThreeSum.EncodedColorLayout.bv,_root_.ThreeSum.EncodedColorLayout.ae,_root_.ThreeSum.EncodedColorLayout.av,_root_.ThreeSum.EncodedColorLayout.class2,_root_.ThreeSum.EncodedColorLayout.class1,_root_.ThreeSum.EncodedColorLayout.class0,_root_.ThreeSum.EncodedColorLayout.colors] <;> ring
  have hfullZ : (free : ℤ)+17+13*(n : ℤ)+5*(_root_.ThreeSum.ColorBandBounds.count n g : ℤ)+
      3*(g : ℤ)*(_root_.ThreeSum.ColorBandBounds.count n g : ℤ)+1 ≤ lim.word := by
    exact (by exact_mod_cast hfull : _ ≤ (lim.space : ℤ)).trans hw
  have hdivWord : ((n-1+g+2 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightEncodedColorLayout.word; omega)).trans hword
  have hR : (_root_.ThreeSum.ColorBandBounds.count n g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightEncodedColorLayout.word; omega)).trans hword
  have hbandsPos : 0 < _root_.ThreeSum.BandPartition.size n g := by
    simp only [_root_.ThreeSum.BandPartition.size,if_neg (by omega : n ≠ 0)]
    exact Nat.zero_lt_succ _
  have hRPos : 0 < _root_.ThreeSum.ColorBandBounds.count n g := by unfold _root_.ThreeSum.ColorBandBounds.count; positivity
  have hthree : 3*_root_.ThreeSum.BandPartition.size n g ≤ _root_.ThreeSum.ColorBandBounds.count n g := by
    have hh := Nat.le_mul_of_pos_right (_root_.ThreeSum.BandPartition.size n g) hbandsPos
    unfold _root_.ThreeSum.ColorBandBounds.count
    nlinarith
  have hthreeZ : 3*(_root_.ThreeSum.BandPartition.size n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast hthree : _ ≤ (ColorBandBounds.count n g : ℤ)).trans hR
  have hsizeEq : (n-1)/g+1=_root_.ThreeSum.BandPartition.size n g := by simp only [_root_.ThreeSum.BandPartition.size,if_neg (by omega : n ≠ 0)]
  have hRZ : 3*(_root_.ThreeSum.BandPartition.size n g : ℤ)*(_root_.ThreeSum.BandPartition.size n g : ℤ)=(_root_.ThreeSum.ColorBandBounds.count n g : ℤ) := by
    simp only [_root_.ThreeSum.ColorBandBounds.count,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,pow_two]
    ring
  have hprod : 3*g*_root_.ThreeSum.ColorBandBounds.count n g ≤ lim.space := by omega
  have h3g : 3*g ≤ lim.space := (Nat.le_mul_of_pos_right (3*g) hRPos).trans hprod
  have h3gZ : 3*(g : ℤ) ≤ lim.word := (by exact_mod_cast h3g : _ ≤ (lim.space : ℤ)).trans hw
  have hprodZ : 3*(g : ℤ)*(_root_.ThreeSum.ColorBandBounds.count n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprod : _ ≤ (lim.space : ℤ)).trans hw
  have hp0 : (0 : ℤ) ≤ 3*(g : ℤ)*(_root_.ThreeSum.ColorBandBounds.count n g : ℤ) := by positivity
  have hvalsZ : (_root_.ThreeSum.EncodedColorLayout.vals free n g : ℤ)=(free : ℤ)+17+13*(n : ℤ)+5*(_root_.ThreeSum.ColorBandBounds.count n g : ℤ) := by
    simp only [_root_.ThreeSum.EncodedColorLayout.vals,_root_.ThreeSum.EncodedColorLayout.rec,_root_.ThreeSum.EncodedColorLayout.tables,_root_.ThreeSum.EncodedColorLayout.ce,_root_.ThreeSum.EncodedColorLayout.cv,_root_.ThreeSum.EncodedColorLayout.be,_root_.ThreeSum.EncodedColorLayout.bv,_root_.ThreeSum.EncodedColorLayout.ae,_root_.ThreeSum.EncodedColorLayout.av,_root_.ThreeSum.EncodedColorLayout.class2,_root_.ThreeSum.EncodedColorLayout.class1,_root_.ThreeSum.EncodedColorLayout.class0,_root_.ThreeSum.EncodedColorLayout.colors,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hEndEq : (_root_.ThreeSum.EncodedColorLayout.vals free n g : ℤ)+3*(g : ℤ)*(_root_.ThreeSum.ColorBandBounds.count n g : ℤ)=
      (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g : ℤ) := by
    simp only [_root_.ThreeSum.EncodedColorLayout.normalizedEnd,_root_.ThreeSum.LightBandRawA.space,_root_.ThreeSum.LightBandRawA.positionBase,_root_.ThreeSum.LightBandRawA.ownerBase,
      _root_.ThreeSum.LightBandRawA.capacity,Nat.cast_add,Nat.cast_mul]
    ring
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.body _root_.ThreeSum.LightEncodedColorLayout.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) hdiv μ hdivWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) hdiv μ hdivWord) ?_ ?_ ?_ ?_
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
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro q μ₀ ⟨hq, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₀
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.BandPartition.size n g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hq, hsizeEq]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hq, hsizeEq] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hq, hsizeEq] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.ColorBandBounds.count n g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hRZ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hRZ] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hRZ] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.colors free : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.class0 free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.class1 free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.class2 free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.av free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.ae free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.bv free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.be free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.cv free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.ce free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.tables free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.rec free n g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.vals free n g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hEndEq, _root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hEndEq, _root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hEndEq, _root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen free (_root_.ThreeSum.EncodedColorLayout.av free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 1) (_root_.ThreeSum.EncodedColorLayout.ae free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 2) (_root_.ThreeSum.EncodedColorLayout.bv free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 3) (_root_.ThreeSum.EncodedColorLayout.be free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 4) (_root_.ThreeSum.EncodedColorLayout.cv free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 5) (_root_.ThreeSum.EncodedColorLayout.ce free n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 6) (_root_.ThreeSum.EncodedColorLayout.rec free n g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (free + 7) (_root_.ThreeSum.EncodedColorLayout.vals free n g : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.EncodedColorLayout.vals, _root_.ThreeSum.EncodedColorLayout.rec, _root_.ThreeSum.EncodedColorLayout.tables, _root_.ThreeSum.EncodedColorLayout.ce, _root_.ThreeSum.EncodedColorLayout.cv, _root_.ThreeSum.EncodedColorLayout.be, _root_.ThreeSum.EncodedColorLayout.bv, _root_.ThreeSum.EncodedColorLayout.ae, _root_.ThreeSum.EncodedColorLayout.av, _root_.ThreeSum.EncodedColorLayout.class2, _root_.ThreeSum.EncodedColorLayout.class1, _root_.ThreeSum.EncodedColorLayout.class0, _root_.ThreeSum.EncodedColorLayout.colors] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.EncodedColorLayout.normalizedEnd free n g : ℕ) ?_ ?_ ?_
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
  exact ⟨rfl,_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.headMemory_heads μ free n g,_root_.ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.headMemory_kept μ free n g⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.meets__implementation_bf583d8cf2) := (@ThreeSum1960614.Machine.ThreeSum.LightEncodedColorLayout.meets__implementation_bf583d8cf2)

#print axioms solution
