-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T05:48:22.949921+00:00
-- url     : https://prove2.me/submissions/0b5c31aa-be83-422a-afed-f427aef7133e

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
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
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
import Mathlib.Data.List.Pi
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

namespace Filter
end Filter
namespace Light
end Light
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.EncodedColorParameterData
end ThreeSum.EncodedColorParameterData
namespace ThreeSum.LightGlobalSizes
end ThreeSum.LightGlobalSizes
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData
end ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
end ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes
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





















































noncomputable section







































































theorem muZero_eq_twice_half (n : ℕ) : _root_.ThreeSum.Scales.muZero n = 2 * _root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) := rfl































































end

end ThreeSum.Scales

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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































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
















theorem localCount_pow (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n ^ _root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) = _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n := by
  have hwidth : 232*_root_.ThreeSum.Scales.muZero n = 464*_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) := by
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_eq_twice_half]
    ring
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs
  rw [hwidth,_root_.ThreeSum1960614.Machine.ThreeSum.Scales.muZero_eq_twice_half]
  rfl

theorem values_scales (n : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.localRadix n) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n)) (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n) =
      [(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.typedOutputs n : ℤ),_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot n,
        _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor n,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values,_root_.ThreeSum.LightGlobalSizes.root,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.localCount_pow,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.divisor,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.band,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.numerator,
    _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandRoot,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandDivisor,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandExponent,
    _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.exponent,_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize,Nat.ceilDiv_eq_add_pred_div]

end ThreeSum.LightGlobalSizes

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
section

theorem ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads__implementation_de05124ab6 {μ : ℕ → ℤ} {params n : ℕ} (H : _root_.ThreeSum1960614.Machine.Light.Seg μ params (_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values n)) :
    μ params=(_root_.ThreeSum.Scales.inputBits n : ℤ) ∧ μ (params+1)=(_root_.ThreeSum.Scales.microHalf (_root_.ThreeSum.Scales.inputBits n) : ℤ) ∧
    μ (params+3)=(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.blockCount (_root_.ThreeSum.Scales.inputBits n) : ℤ) ∧ μ (params+4)=(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.mu n : ℤ) ∧
    μ (params+14)=(_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n : ℤ) ∧ μ (params+17)=(_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n : ℤ) ∧
    μ (params+18)=(_root_.ThreeSum.Scales.primeWindow n : ℤ) := by
  have h (i : ℕ) (hi : i < 19) := H.getD (i := i)
    (by simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using h 0 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using h 1 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using h 3 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values] using h 4 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values_scales] using h 14 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values_scales] using h 17 (by omega)
  · simpa [_root_.ThreeSum1960614.Machine.ThreeSum.LightParameterInit.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightScales.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalParameters.values,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCounts.values,
      _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalSizes.values_scales] using h 18 (by omega)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads__implementation_de05124ab6) := (@ThreeSum1960614.Machine.ThreeSum.EncodedColorParameterData.reads__implementation_de05124ab6)

#print axioms solution
