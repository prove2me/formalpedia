-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightParameterInit.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:08:41.298835+00:00
-- url     : https://prove2.me/submissions/8aec6711-2068-4177-a18d-879944f05aa5

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
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
import Definitions.Def_ThreeSum1962Source_Bundle12
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pi
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
import Mathlib.LinearAlgebra.Matrix.ToLin
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
import Theorems.Thm_Light_seg_append
import Theorems.Thm_Light_seg_cons
import Theorems.Thm_ThreeSum1960614_Machine_Light_sqrt_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightGlobalSizes_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalParameters_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightNatPower_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightScales_meets

local instance platformRadixNonzero_c9e4e8670e (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


private theorem platform_seg_cons_c9e4e8670e {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

private theorem platform_seg_append_c9e4e8670e {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_c9e4e8670e (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightGlobalSizes
end ThreeSum.LightGlobalSizes
namespace ThreeSum.LightParameterInit
end ThreeSum.LightParameterInit
namespace ThreeSum.LightScales
end ThreeSum.LightScales
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
end ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
namespace ThreeSum1960614.Machine.ThreeSum.LightParameterInit
end ThreeSum1960614.Machine.ThreeSum.LightParameterInit
namespace ThreeSum1960614.Machine.ThreeSum.LightScales
end ThreeSum1960614.Machine.ThreeSum.LightScales
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
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















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]





/-- Writing outside a segment. -/
theorem Seg.update_out (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (hb : b < a ∨ a + l.length ≤ b) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ b x) a l :=
  h.congr fun i hi => Function.update_of_ne (by omega) _ _

/-- Writing just after a segment makes it longer. -/
theorem Seg.snoc (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (x : ℤ) : _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ (a + l.length) x) a (l ++ [x]) :=
  platform_seg_append_c9e4e8670e.2 ⟨h.update_out (Or.inr le_rfl) x, by simp [platform_seg_cons_c9e4e8670e]⟩













































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Executing global powers and rounded band sizes

This routine consumes the already computed local output count, local prime,
block count, and total inner size. All global powers, the square-root
rounding, and the final ceiling division are actual Light computations.
The square-root loop and quotient loop are included in the stated time.
-/

namespace ThreeSum.LightGlobalSizes
open _root_.ThreeSum.LightGlobalSizes


set_option maxHeartbeats 1000000

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds

















variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}














theorem localCount_pos (n : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n := Nat.choose_pos (by omega)





end ThreeSum.LightGlobalSizes

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





















theorem Procs.meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.Procs P pMain)
    {μ : ℕ → ℤ} {n dst d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : dst+5 ≤ lim.space)
    (hword : ((35000000000*(n+1) : ℕ) : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [n,dst] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.time n)
      (fun r μ' => r = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst 5) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.meets S.main S.log S.cube S.half S.divide hw hspace hword hd

end ThreeSum.LightScales

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightParameterInit
open _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightParameterInit.Procs.meets__implementation_55c66caf59 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.Procs P pMain)
    {μ : ℕ → ℤ} {n dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*_root_.ThreeSum.LightParameterInit.half n+6 ≤ lim.depth)
    (hout : dst+19 ≤ work) (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.space work n ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [n,dst,work] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time n)
      (fun r μ' => r = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work dst 19) := by
  have hCoreWord : ((35000000000*(n+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 35000000000*(n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hLocalWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.word (_root_.ThreeSum.LightParameterInit.half n) : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.word (_root_.ThreeSum.LightParameterInit.half n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hGlobalWord : (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hAuxWord : ((100*(_root_.ThreeSum.Scales.primeWindow n+_root_.ThreeSum.Scales.inputBits n+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 100*(_root_.ThreeSum.Scales.primeWindow n+_root_.ThreeSum.Scales.inputBits n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwork : work ≤ lim.space := by
    have hh : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.space work (_root_.ThreeSum.LightParameterInit.half n) ≤ lim.space :=
      (le_max_left _ _).trans hspace
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.space at hh
    omega
  have hbits := _root_.ThreeSum1960614.Machine.ThreeSum.LightScales.inputBits_le_self n
  have hhalf : _root_.ThreeSum.LightParameterInit.half n ≤ n := (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.microHalf_le_self (_root_.ThreeSum.Scales.inputBits n)).trans hbits
  have hmu : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n ≤ n := (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.totalSize_le_self (_root_.ThreeSum.Scales.inputBits n)).trans hbits
  have hJ : _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) ≤ 20*n :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.blockCount_le _).trans (Nat.mul_le_mul_left _ hbits)
  have hglobalBound (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n)
      (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hGlobalWord
  have hCWord := hglobalBound (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hpWord := hglobalBound (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word; omega)
  have hRWord : (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) ≤ lim.word :=
    hglobalBound (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.word _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix; omega)
  have hWindowWord : (_root_.ThreeSum.Scales.primeWindow n : ℤ) ≤ lim.word := by omega
  have hsqrt := Nat.sqrt_le_self (_root_.ThreeSum.Scales.inputBits n)
  have he : _root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n) ≤ _root_.ThreeSum.Scales.inputBits n+1 := by unfold _root_.ThreeSum.Scales.windowExponent; omega
  have heWord : (_root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n) : ℤ) ≤ lim.word := by omega
  have hWindowPowers (i : ℕ) (hi : i ≤ _root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n)) :
      ((2^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hWindowWord
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.body _root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((S.core.meets (d := d + 1) (μ := μ) (n := n) (dst := dst) hw (by omega) hCoreWord (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (S.core.meets (d := d + 1) (μ := μ) (n := n) (dst := dst) hw (by omega) hCoreWord (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time] <;> omega)
     on_goal -1 => (rintro total μ₁ ⟨htotal, hcore, hkept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hhalfRead : μ₁ (dst+1) = (_root_.ThreeSum.LightParameterInit.half n : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum.LightParameterInit.half] using hcore 1 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values])
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightParameterInit.half n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hhalfRead, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hhalfRead, _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hhalfRead, _root_.ThreeSum.LightNatPower.time] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((S.localParams.meets (d := d + 1) (μ := μ₁) (h := _root_.ThreeSum.LightParameterInit.half n) (dst := dst + 5) (work := work) hw (by omega) (by omega) hspace hLocalWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (S.localParams.meets (d := d + 1) (μ := μ₁) (h := _root_.ThreeSum.LightParameterInit.half n) (dst := dst + 5) (work := work) hw (by omega) (by omega) hspace hLocalWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time] <;> omega)
     on_goal -1 => (rintro pval μ₂ ⟨hpval, hlocal, hkept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hpval' : pval = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n : ℤ) := hpval
  have hcore₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n) := by
    apply hcore.congr
    intro i hi
    have hi' : i < 5 := by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using hi
    exact hkept₂ _ ⟨by omega,Or.inl (by omega)⟩
  have hprefix₂ : _root_.ThreeSum1960614.Machine.Light.Seg μ₂ dst (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n ++ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values (_root_.ThreeSum.LightParameterInit.half n)) := by
    apply platform_seg_append_c9e4e8670e.mpr
    exact ⟨hcore₂,by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using hlocal⟩
  have hJread : μ₂ (dst+3) = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using hcore₂ 3 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values])
  have hCread : μ₂ (dst+5) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum.LightParameterInit.half,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount]
      using hlocal 0 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values])
  have hJnat : ((dst : ℤ)+3).toNat = dst+3 := by
    rw [show (dst : ℤ)+3 = ((dst+3 : ℕ) : ℤ) by omega,Int.toNat_natCast]
  have hCnat : ((dst : ℤ)+5).toNat = dst+5 := by
    rw [show (dst : ℤ)+5 = ((dst+5 : ℕ) : ℤ) by omega,Int.toNat_natCast]
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hJnat, hJread, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hJnat, hJread, _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hJnat, hJread, _root_.ThreeSum.LightNatPower.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hCnat, hCread, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hCnat, hCread, _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hCnat, hCread, _root_.ThreeSum.LightNatPower.time] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((S.globalSizes.meets (d := d + 1) (μ := μ₂) (C := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (p := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n) (J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (mu := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (dst := dst + 13) hw (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount_pos n) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos (_root_.ThreeSum.LightParameterInit.half n)) (by omega) hGlobalWord) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (S.globalSizes.meets (d := d + 1) (μ := μ₂) (C := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (p := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n) (J := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (mu := _root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) (dst := dst + 13) hw (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount_pos n) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos (_root_.ThreeSum.LightParameterInit.half n)) (by omega) hGlobalWord) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpval', htotal, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hpval', htotal, _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpval', htotal, _root_.ThreeSum.LightNatPower.time] <;> omega)
     on_goal -1 => (rintro rglobal μ₃ ⟨hglobalResult, hglobal, hkept₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hglobalResult' : rglobal = (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) := hglobalResult
  have hprefix₃ : _root_.ThreeSum1960614.Machine.Light.Seg μ₃ dst
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n ++ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values (_root_.ThreeSum.LightParameterInit.half n)) := by
    apply hprefix₂.congr
    intro i hi
    have hi' : i < 13 := by
      simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values] using hi
    exact hkept₃ _ (Or.inl (by omega))
  have hfull : _root_.ThreeSum1960614.Machine.Light.Seg μ₃ dst
      ((_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values n ++ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values (_root_.ThreeSum.LightParameterInit.half n)) ++
        _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n)
          (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n)) := by
    apply platform_seg_append_c9e4e8670e.mpr
    exact ⟨hprefix₃,by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values] using hglobal⟩
  have hbitsRead : μ₃ dst = (_root_.ThreeSum.Scales.inputBits n : ℤ) := by
    simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using hprefix₃ 0 (by simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values])
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.Scales.inputBits n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbitsRead, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbitsRead, _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbitsRead, _root_.ThreeSum.LightNatPower.time] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.sqrt_meets (d := d + 1) (K := _root_.ThreeSum.Scales.inputBits n) S.sqrt μ₃ (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.sqrt_meets (d := d + 1) (K := _root_.ThreeSum.Scales.inputBits n) S.sqrt μ₃ (by omega)) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time] <;> omega)
     on_goal -1 => (rintro rt μ₄ ⟨hrt, hmem₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₄
  have hrt' : rt+1 = (_root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n) : ℤ) := by
    simpa [_root_.ThreeSum.Scales.windowExponent] using congrArg (fun z : ℤ => z+1) hrt
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrt', _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hrt', _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrt', _root_.ThreeSum.LightNatPower.time] <;> omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) (b := 2) (e := _root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n)) S.power μ₃ heWord hWindowPowers) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightNatPower.meets (d := d + 1) (b := 2) (e := _root_.ThreeSum.Scales.windowExponent (_root_.ThreeSum.Scales.inputBits n)) S.power μ₃ heWord hWindowPowers) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNatPower.time] <;> omega)
     on_goal -1 => (rintro window μ₅ ⟨hwindow, hmem₅⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₅
  have hwindow' : window = (_root_.ThreeSum.Scales.primeWindow n : ℤ) := hwindow
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 18) (_root_.ThreeSum.Scales.primeWindow n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hwindow', _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hwindow', _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hwindow', _root_.ThreeSum.LightNatPower.time] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hglobalResult', _root_.ThreeSum.LightNatPower.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hglobalResult', _root_.ThreeSum.LightNatPower.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hglobalResult', _root_.ThreeSum.LightNatPower.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨rfl,?_,?_⟩
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values] using hfull.snoc (_root_.ThreeSum.Scales.primeWindow n : ℤ)
  · intro a ha
    change Function.update μ₃ (dst+18) _ a = μ a
    rw [Function.update_of_ne (by omega)]
    exact (hkept₃ a (by omega)).trans
      ((hkept₂ a ⟨ha.1,by omega⟩).trans (hkept₁ a (by omega)))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightParameterInit.Procs.meets__implementation_55c66caf59) := (@ThreeSum1960614.Machine.ThreeSum.LightParameterInit.Procs.meets__implementation_55c66caf59)

#print axioms solution
