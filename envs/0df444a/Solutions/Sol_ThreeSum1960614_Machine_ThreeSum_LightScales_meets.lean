-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightScales.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T08:58:55.134619+00:00
-- url     : https://prove2.me/submissions/ecb1b5da-4755-49aa-a8c5-475e842d866d

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
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
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_cbrtCeil_meets
import Theorems.Thm_ThreeSum1960614_Machine_Light_half_meets
import Theorems.Thm_ThreeSum1960614_Machine_Light_log2_meets
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets

private theorem platform_seg_cons_b4be7b9999 {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

@[simp] private theorem platform_seg_nil_b4be7b9999 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Filter
end Filter
namespace Light
end Light
namespace Light.Logs
end Light.Logs
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Logs
end ThreeSum1960614.Machine.Light.Logs
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales
open _root_.ThreeSum.Scales


open _root_.Filter
open _root_.Real
open scoped _root_.Topology

















































theorem totalSize_upper (m : ℕ) : 1000000000 * _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize m ≤ 203889696 * m := by
  have h := Nat.div_mul_le_self (203889696 * m) (20000000000 * _root_.ThreeSum.Scales.microSize m)
  convert h using 1 <;> simp only [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize, _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount] <;> ring



noncomputable section







































































































































end

end ThreeSum.Scales

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

namespace ThreeSum1960614.Machine

/-!
# Logarithms, the cube root and halves, without division

Four routines on local variables only; none of them touches the memory.

* log2(x) returns ⌊log₂ x⌋ (0 for x = 0) by doubling (`log2_meets`).
* clog2(x) returns ⌈log₂ x⌉ (0 for x ≤ 1) by doubling (`clog2_meets`).
* cbrtCeil(n) returns the least s with s³ ≥ n, which is ⌈n^{1/3}⌉, by counting up
  (`cbrtCeil_meets`).
* half(h) returns ⌈h/2⌉ by counting up (`half_meets`).

Each of them is one loop that tries the candidates 0, 1, 2, … in turn.  Local variable 0 holds the
argument and receives the result, local variable 1 holds the candidate (`Arg`, `Cand`), and the two
logarithms keep a power of two in local variable 2 (`Power`).
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

namespace Logs
open _root_.Light.Logs






end Logs

open _root_.Light.Logs
open _root_.ThreeSum1960614.Machine.Light.Logs

/-! ## The logarithm, rounded down -/







/-! ## The logarithm, rounded up -/







/-! ## The cube root, rounded up -/





theorem le_cbrtLeast_pow (n : ℕ) : n ≤ _root_.Light.cbrtLeast n ^ 3 := Nat.find_spec (_root_.Light.exists_le_cube n)



theorem cbrtLeast_le {n s : ℕ} (h : n ≤ s ^ 3) : _root_.Light.cbrtLeast n ≤ s :=
  Nat.find_min' (_root_.Light.exists_le_cube n) h

theorem cbrtLeast_le_self (n : ℕ) : _root_.Light.cbrtLeast n ≤ n :=
  _root_.ThreeSum1960614.Machine.Light.cbrtLeast_le (Nat.le_self_pow (by norm_num) n)













/-! ## Halves, rounded up -/







end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales
open _root_.ThreeSum.LightScales


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem inputBits_le_self (n : ℕ) : _root_.ThreeSum.Scales.inputBits n ≤ n := by
  simpa [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using Nat.log_le_self 2 n

theorem root_le_self (m : ℕ) : Nat.nthRoot 3 m ≤ m :=
  (Nat.le_self_pow (by decide : 3 ≠ 0) (Nat.nthRoot 3 m)).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))

theorem microSize_le_self (m : ℕ) : _root_.ThreeSum.Scales.microSize m ≤ m :=
  (_root_.ThreeSum.Scales.microSize_rounding m).1.trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.root_le_self m)

theorem microHalf_le_self (m : ℕ) : _root_.ThreeSum.Scales.microHalf m ≤ m :=
  (Nat.div_le_self (Nat.nthRoot 3 m) 2).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.root_le_self m)

theorem blockCount_le (m : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m ≤ 20*m := by
  by_cases hs : _root_.ThreeSum.Scales.microSize m=0
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount,hs]
  · have hspos : 1 ≤ _root_.ThreeSum.Scales.microSize m := by omega
    have hJ : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m ≤ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m*_root_.ThreeSum.Scales.microSize m := by
      calc
        _ = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount m*1 := by ring
        _ ≤ _ := Nat.mul_le_mul_left _ hspos
    have hu := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize_upper m
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize at hu
    omega

theorem totalSize_le_self (m : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize m ≤ m := by
  have h := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize_upper m
  omega

theorem cbrtLeast_successor (m : ℕ) : _root_.Light.cbrtLeast (m+1) = Nat.nthRoot 3 m+1 := by
  have hlo : Nat.nthRoot 3 m ^ 3 ≤ m := Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0))
  have hhi : m < (Nat.nthRoot 3 m+1)^3 := Nat.lt_pow_nthRoot_add_one (by decide) m
  have hup : _root_.Light.cbrtLeast (m+1) ≤ Nat.nthRoot 3 m+1 := _root_.ThreeSum1960614.Machine.Light.cbrtLeast_le (by omega)
  have hstrict : Nat.nthRoot 3 m < _root_.Light.cbrtLeast (m+1) := by
    by_contra h
    have hp := Nat.pow_le_pow_left (show _root_.Light.cbrtLeast (m+1) ≤ Nat.nthRoot 3 m by omega) 3
    have hneed := _root_.ThreeSum1960614.Machine.Light.le_cbrtLeast_pow (m+1)
    omega
  omega

theorem half_cbrtLeast (m : ℕ) : (_root_.Light.cbrtLeast (m+1)+1)/2 = _root_.ThreeSum.Scales.microHalf m+1 := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.cbrtLeast_successor]
  unfold _root_.ThreeSum.Scales.microHalf
  omega



















end ThreeSum.LightScales

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightScales

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightScales.meets__implementation_ca414164f1 {pMain pLog pCube pHalf pDiv : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.body pLog pCube pHalf pDiv))
    (hlog : P[pLog]? = some _root_.ThreeSum1960614.Machine.Light.log2Body)
    (hcube : P[pCube]? = some _root_.ThreeSum1960614.Machine.Light.cbrtCeilBody)
    (hhalf : P[pHalf]? = some _root_.ThreeSum1960614.Machine.Light.halfBody)
    (hdiv : P[pDiv]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((35000000000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [n,dst] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time n)
      (fun r μ' => r = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst 5) := by
  have hm : (_root_.ThreeSum.Scales.inputBits n) ≤ n := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.inputBits_le_self n
  have hm₀ : _root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) ≤ (_root_.ThreeSum.Scales.inputBits n) := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.microSize_le_self (_root_.ThreeSum.Scales.inputBits n)
  have hh : _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) ≤ (_root_.ThreeSum.Scales.inputBits n) := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.microHalf_le_self (_root_.ThreeSum.Scales.inputBits n)
  have hJ : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) ≤ 20*(_root_.ThreeSum.Scales.inputBits n) := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.blockCount_le (_root_.ThreeSum.Scales.inputBits n)
  have hmu : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize (_root_.ThreeSum.Scales.inputBits n) ≤ (_root_.ThreeSum.Scales.inputBits n) := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.totalSize_le_self (_root_.ThreeSum.Scales.inputBits n)
  have hu : _root_.Light.cbrtLeast ((_root_.ThreeSum.Scales.inputBits n)+1) ≤ (_root_.ThreeSum.Scales.inputBits n)+1 := _root_.ThreeSum1960614.Machine.Light.cbrtLeast_le_self ((_root_.ThreeSum.Scales.inputBits n)+1)
  have hall (x : ℕ) (hx : x ≤ 35000000000*(n+1)) : (x : ℤ) ≤ lim.word := by
    have hz : (x : ℤ) ≤ ((35000000000*(n+1) : ℕ) : ℤ) := by exact_mod_cast hx
    exact hz.trans hword
  have hmWord := hall (_root_.ThreeSum.Scales.inputBits n) (by omega)
  have hhWord := hall (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)) (by omega)
  have hm₀Word := hall (_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n)) (by omega)
  have hJWord := hall (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (by omega)
  have hmuWord := hall (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize (_root_.ThreeSum.Scales.inputBits n)) (by omega)
  have hnumWord : (203889696 : ℤ)*(_root_.ThreeSum.Scales.inputBits n : ℤ) ≤ lim.word := by
    simpa using hall (203889696*_root_.ThreeSum.Scales.inputBits n) (by omega)
  have hdenWord : (20000000000 : ℤ)*(_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ) ≤ lim.word := by
    simpa using hall (20000000000*_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n)) (by omega)
  have hproductWord : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℤ)*(_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ) ≤ lim.word := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize] using hmuWord
  have hproductNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℤ)*(_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ) := by positivity
  have hsizeEq : (2 : ℤ)*(_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) : ℤ) = (_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ) := by
    simp [_root_.ThreeSum.Scales.microSize,_root_.ThreeSum.Scales.microHalf]
  have hcountEq : (20 : ℤ)*((203889696*_root_.ThreeSum.Scales.inputBits n/(20000000000*_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n)) : ℕ) : ℤ) =
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℤ) := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount]
  have hproductEq : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℤ)*(_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ) =
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize (_root_.ThreeSum.Scales.inputBits n) : ℤ) := by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize]
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.body _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time
  have hlogCall := _root_.ThreeSum1960614.Machine.Light.log2_meets (d := d+1) (x := n) hlog μ (hall _ (by omega))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hlogCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hlogCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro bits μ₁ ⟨hbits, hmem₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₁
  have hbits' : bits = ((_root_.ThreeSum.Scales.inputBits n) : ℤ) := by simpa [_root_.ThreeSum.Scales.inputBits,Nat.log2_eq_log_two] using hbits
  have hcubeCall := _root_.ThreeSum1960614.Machine.Light.cbrtCeil_meets (d := d+1) (n := (_root_.ThreeSum.Scales.inputBits n)+1) hcube μ (hall _ (by omega))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcubeCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcubeCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro cube μ₂ ⟨hc, hmem₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₂
  have hhalfCall := _root_.ThreeSum1960614.Machine.Light.half_meets (d := d+1) (h := _root_.Light.cbrtLeast ((_root_.ThreeSum.Scales.inputBits n)+1)) hhalf μ (hall _ (by omega))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hhalfCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hhalfCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hc, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hc, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     on_goal -1 => (rintro half μ₃ ⟨hv, hmem₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₃
  have hv' : half = ((_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n)+1 : ℕ) : ℤ) := by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.half_cbrtLeast] using hv
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hv', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hv', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hv', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsizeEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hsizeEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsizeEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hdivCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d+1)
    (a := 203889696*_root_.ThreeSum.Scales.inputBits n) (b := 20000000000*_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n))
    hdiv μ (hall _ (by omega))
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hdivCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hdivCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
     on_goal -1 => (rintro q μ₄ ⟨hq, hmem₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₄
  have hquotNonneg : (0 : ℤ) ≤ (203889696*(_root_.ThreeSum.Scales.inputBits n : ℤ))/(20000000000*(_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using
      (Int.natCast_nonneg (203889696*_root_.ThreeSum.Scales.inputBits n/(20000000000*_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n))))
  have hquotWord : (20 : ℤ)*((203889696*(_root_.ThreeSum.Scales.inputBits n : ℤ))/(20000000000*(_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ))) ≤ lim.word := by
    simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount,Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using hJWord
  have hqZ : q = (203889696*(_root_.ThreeSum.Scales.inputBits n : ℤ))/(20000000000*(_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℤ)) := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Int.natCast_ediv] using hq
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hqZ, hcountEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hqZ, hcountEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hqZ, hcountEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hproductEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hproductEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hproductEq, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst ((_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbits', _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 2) (_root_.ThreeSum.Scales.microSize (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 3) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 4) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.totalSize (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.cbrtCeilTime, _root_.Light.halfTime, _root_.ThreeSum.LightSmallDivide.time, _root_.ThreeSum.Scales.muZero] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨by simp [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu],?_,by 
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
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,platform_seg_cons_b4be7b9999,_root_.ThreeSum.Scales.muZero,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightScales.meets__implementation_ca414164f1) := (@ThreeSum1960614.Machine.ThreeSum.LightScales.meets__implementation_ca414164f1)

#print axioms solution
