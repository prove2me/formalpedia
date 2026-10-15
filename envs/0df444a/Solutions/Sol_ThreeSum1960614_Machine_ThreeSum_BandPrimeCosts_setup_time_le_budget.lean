-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.setup_time_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T09:15:34.291436+00:00
-- url     : https://prove2.me/submissions/2720e62f-e719-4499-95d9-ffce65cf3445

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
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
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
import Theorems.Thm_ThreeSum_BandPrimeCosts_aggregate_time_le
import Theorems.Thm_ThreeSum_ModuloCosts_time_bound

local instance platformRadixNonzero_64ea1aa092 (n : ℕ) : NeZero (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) :=
  ⟨Nat.ne_of_gt (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix_pos n)⟩


namespace Filter
end Filter
namespace Light
end Light
namespace Polynomial
end Polynomial
namespace Real
end Real
namespace ThreeSum
end ThreeSum
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandPrimeCosts
end ThreeSum.BandPrimeCosts
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightBandPrimeDepth
end ThreeSum.LightBandPrimeDepth
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.ModuloRuntime
end ThreeSum.ModuloRuntime
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
end ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
namespace ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts
end ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts
namespace ThreeSum1960614.Machine.ThreeSum.BandScales
end ThreeSum1960614.Machine.ThreeSum.BandScales
namespace ThreeSum1960614.Machine.ThreeSum.CostLedger
end ThreeSum1960614.Machine.ThreeSum.CostLedger
namespace ThreeSum1960614.Machine.ThreeSum.HierarchyScales
end ThreeSum1960614.Machine.ThreeSum.HierarchyScales
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
end ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
end ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
namespace ThreeSum1960614.Machine.ThreeSum.MassScales
end ThreeSum1960614.Machine.ThreeSum.MassScales
namespace ThreeSum1960614.Machine.ThreeSum.ModuloCosts
end ThreeSum1960614.Machine.ThreeSum.ModuloCosts
namespace ThreeSum1960614.Machine.ThreeSum.ModuloRuntime
end ThreeSum1960614.Machine.ThreeSum.ModuloRuntime
namespace ThreeSum1960614.Machine.ThreeSum.Parameters
end ThreeSum1960614.Machine.ThreeSum.Parameters
namespace ThreeSum1960614.Machine.ThreeSum.Scales
end ThreeSum1960614.Machine.ThreeSum.Scales
namespace ThreeSum1960614.Machine.ThreeSum.StageBounds
end ThreeSum1960614.Machine.ThreeSum.StageBounds
namespace ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
end ThreeSum1960614.Machine.ThreeSum.UniformStageBounds

namespace ThreeSum1960614.Machine

/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface
open _root_.ThreeSum.KaratsubaInterface


open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
open _root_.Polynomial



theorem le_capacity (p : ℕ) : p ≤ _root_.ThreeSum.KaratsubaInterface.capacity p := Nat.le_pow_clog (by decide) p

























end ThreeSum.KaratsubaInterface

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compute the prescribed common-prime depth without division

The loop compares successive `4*(4*y)^(i+1)` with the radix. It returns
exactly `Nat.log (4*y) (R/4)`, including the zero-depth case. Only local
variables change, and the number of iterations is that logarithm.
-/

namespace ThreeSum.LightBandPrimeDepth
open _root_.ThreeSum.LightBandPrimeDepth


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000








variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}







theorem depth_eq_primeDepth (n : ℕ) :
    _root_.ThreeSum.LightBandPrimeDepth.depth (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n)=_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n := rfl

end ThreeSum.LightBandPrimeDepth

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Uniform bounds for repeated modular-counting calls

A caller may reserve resources for the largest modulus it will use. These
lemmas relate that reservation to the exact costed program contract.
-/

namespace ThreeSum.ModuloRuntime
open _root_.ThreeSum.ModuloRuntime


open _root_.ThreeSum.LightModuloCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LightModuloCounts
open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface

theorem capacity_mono {p q : ℕ} (h : p ≤ q) : _root_.ThreeSum.KaratsubaInterface.capacity p ≤ _root_.ThreeSum.KaratsubaInterface.capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

theorem karatsuba_time_mono : Monotone _root_.ThreeSum.LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum.LightKaratsuba.time]
  omega

theorem time_mono {p q : ℕ} (h : p ≤ q) (nA nB nC U : ℕ) :
    _root_.ThreeSum.LightModuloCounts.time p nA nB nC U ≤ _root_.ThreeSum.LightModuloCounts.time q nA nB nC U := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.capacity_mono h
  have hl := Nat.clog_mono_right 2 h
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.karatsuba_time_mono hl
  unfold _root_.ThreeSum.LightModuloCounts.time _root_.ThreeSum.LightCapacity.time _root_.ThreeSum.LightResidueHistogram.time
    _root_.ThreeSum.LightHistogram.histogramTime _root_.ThreeSum.LightCyclic.combinedTime
  simp only [_root_.Light.fillTime, _root_.ThreeSum.LightArray.linearTime]
  omega









end ThreeSum.ModuloRuntime

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite arithmetic-operation bounds for the complete counting backend

The only input-size dependence outside the Karatsuba term is the number of
original elements times their remainder bit budget. Histogram initialization,
capacity computation and folding are included in the displayed constant.
-/

namespace ThreeSum.ModuloCosts
open _root_.ThreeSum.ModuloCosts


open _root_.ThreeSum.KaratsubaInterface
open _root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface



theorem capacity_le_roundedPower (p : ℕ) : _root_.ThreeSum.KaratsubaInterface.capacity p ≤ _root_.ThreeSum.ModuloCosts.roundedPower p :=
  Nat.pow_le_pow_left (by decide) _









end ThreeSum.ModuloCosts

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum.ArithmeticStageBounds


open _root_.Filter
open _root_.Real
open _root_.ThreeSum.Parameters
open _root_.ThreeSum1960614.Machine.ThreeSum.Parameters
open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.HierarchyScales
open _root_.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.MassScales
open _root_.ThreeSum1960614.Machine.ThreeSum.StageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.UniformStageBounds
open _root_.ThreeSum.ModuloCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts
open scoped _root_.Topology

set_option maxHeartbeats 1000000

















theorem bits_le_window_square (n : ℕ) : _root_.ThreeSum.Scales.inputBits n+1 ≤ _root_.ThreeSum.Scales.primeWindow n^2 := by
  have hroot := Nat.lt_succ_sqrt' (_root_.ThreeSum.Scales.inputBits n)
  have hpow : Nat.sqrt (_root_.ThreeSum.Scales.inputBits n)+1 ≤ 2^(Nat.sqrt (_root_.ThreeSum.Scales.inputBits n)+1) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hs := Nat.pow_le_pow_left hpow 2
  unfold _root_.ThreeSum.Scales.primeWindow _root_.ThreeSum.Scales.windowExponent
  simp only [Nat.succ_eq_add_one] at hroot
  omega

theorem remainder_bits_le {n : ℕ} (k : ℕ) (hn : 0 < n) :
    Nat.log 2 (n^k+1)+1 ≤ _root_.ThreeSum.ArithmeticStageBounds.bitBudget k n := by
  have hp : 0 < n^k := Nat.pow_pos hn
  have hm := Nat.log_mono_right (b := 2) (show n^k+1 ≤ 3*n^k by omega)
  have hl := _root_.ThreeSum.Scales.log2_difference_bound k hn
  rw [Nat.log2_eq_log_two] at hl
  have hw := Nat.mul_le_mul_left (2*(k+2)) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.bits_le_window_square n)
  unfold _root_.ThreeSum.ArithmeticStageBounds.bitBudget
  omega

theorem invocation_le_budget {n p nA nB nC : ℕ} (k : ℕ)
    (hn : 0 < n) (hp : p ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)
    (ha : nA ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (hb : nB ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (hc : nC ≤ _root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) :
    _root_.ThreeSum.LightModuloCounts.time p nA nB nC (n^k) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.ModuloRuntime.time_mono hp nA nB nC (n^k)
  have hbnd := _root_.ThreeSum.ModuloCosts.time_bound (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) nA nB nC (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (n^k) ha hb hc
  have hm := Nat.mul_le_mul_left (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.remainder_bits_le k hn)
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget
  omega

noncomputable section



































end
end ThreeSum.ArithmeticStageBounds

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Charge the executed common-prime setup

The bound includes the generated pool, every aggregate candidate minimum,
all original band-score calls, and the computed chain depth. The size-only
budget uses the same quadratic owner bound as the physical mass theorem.
-/

namespace ThreeSum.BandPrimeCosts
open _root_.ThreeSum.BandPrimeCosts


open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000



theorem unit_ge (p g U : ℕ) : 1000 ≤ _root_.ThreeSum.BandPrimeCosts.unit p g U := by unfold _root_.ThreeSum.BandPrimeCosts.unit; omega





theorem minimum_time_le (p g R s U : ℕ) :
    _root_.ThreeSum.LightBandPrimeMinimum.time p g R s U ≤ 3*(R+1)*(s+1)^2*_root_.ThreeSum.BandPrimeCosts.unit p g U := by
  have hv : 1000 ≤ (R+1)*(s+1)*_root_.ThreeSum.BandPrimeCosts.unit p g U :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.unit_ge p g U).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hh := _root_.ThreeSum.BandPrimeCosts.aggregate_time_le p g R s U
  calc
    _ = (s+1)*(_root_.ThreeSum.LightBandWeightedScore.time p g R s U+140) := by
      unfold _root_.ThreeSum.LightBandPrimeMinimum.time; ring
    _ ≤ (s+1)*(3*((R+1)*(s+1)*_root_.ThreeSum.BandPrimeCosts.unit p g U)) := by
      apply Nat.mul_le_mul_left
      nlinarith
    _ = _ := by ring



theorem core_ge (p g R s U : ℕ) : 1000 ≤ _root_.ThreeSum.BandPrimeCosts.core p g R s U := by
  have hp : 0 < (R+1)*(s+1)^2 := by positivity
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.unit_ge p g U).trans (Nat.le_mul_of_pos_left _ hp)

theorem chain_time_le (p g R s U levels : ℕ) :
    _root_.ThreeSum.LightBandPrimeChain.time p g R s U levels ≤ 4*(levels+1)*_root_.ThreeSum.BandPrimeCosts.core p g R s U := by
  have hm : _root_.ThreeSum.LightBandPrimeMinimum.time p g R s U ≤ 3*_root_.ThreeSum.BandPrimeCosts.core p g R s U := by
    simpa only [_root_.ThreeSum.BandPrimeCosts.core,Nat.mul_assoc] using _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.minimum_time_le p g R s U
  have hh := Nat.mul_le_mul_left levels (Nat.add_le_add_right hm 140)
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.core_ge p g R s U
  unfold _root_.ThreeSum.LightBandPrimeChain.time
  nlinarith

theorem setup_time_le (p g R M y U : ℕ) :
    _root_.ThreeSum.LightBandPrimeSetup.time p g R M y U ≤ _root_.ThreeSum.LightPrimePool.time y+
      5*(_root_.ThreeSum.LightBandPrimeDepth.depth M y+1)*(R+1)*(_root_.ThreeSum.LightPrimePool.size y+1)^2*_root_.ThreeSum.BandPrimeCosts.unit p g U := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.chain_time_le p g R (_root_.ThreeSum.LightPrimePool.size y) U (_root_.ThreeSum.LightBandPrimeDepth.depth M y)
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.core_ge p g R (_root_.ThreeSum.LightPrimePool.size y) U
  have hh : _root_.ThreeSum.LightBandPrimeDepth.time M y+
      _root_.ThreeSum.LightBandPrimeChain.time p g R (_root_.ThreeSum.LightPrimePool.size y) U (_root_.ThreeSum.LightBandPrimeDepth.depth M y)+240 ≤
      5*(_root_.ThreeSum.LightBandPrimeDepth.depth M y+1)*_root_.ThreeSum.BandPrimeCosts.core p g R (_root_.ThreeSum.LightPrimePool.size y) U := by
    unfold _root_.ThreeSum.LightBandPrimeDepth.time
    nlinarith
  unfold _root_.ThreeSum.LightBandPrimeSetup.time _root_.ThreeSum.LightBandPrimeConstruction.time
  simp only [_root_.ThreeSum.BandPrimeCosts.core,Nat.mul_assoc] at hh ⊢
  omega



theorem unit_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    _root_.ThreeSum.BandPrimeCosts.unit (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) (n^k) ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.invocation_le_budget (p := _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) k hn le_rfl le_rfl le_rfl le_rfl
  have hp := (_root_.ThreeSum1960614.Machine.ThreeSum.KaratsubaInterface.le_capacity (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.ModuloCosts.capacity_le_roundedPower (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n))
  have hl : Nat.log 2 (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n+1 := Nat.log_le_self _ _
  have hj : _root_.ThreeSum.LightWeightedScore.jointTime (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by
    unfold _root_.ThreeSum.LightWeightedScore.jointTime _root_.ThreeSum.LightResidues.residueBudget _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget
    omega
  have hlarge : 1000 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n := by unfold _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget; omega
  unfold _root_.ThreeSum.BandPrimeCosts.unit
  omega





end ThreeSum.BandPrimeCosts

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.BandPrimeCosts
open _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts

open _root_.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.Scales
open _root_.ThreeSum1960614.Machine.ThreeSum.BandScales
open _root_.ThreeSum.CostLedger
open _root_.ThreeSum1960614.Machine.ThreeSum.CostLedger
open _root_.ThreeSum.ArithmeticStageBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
section

theorem ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.setup_time_le_budget__implementation_df86a00035 {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2) :
    _root_.ThreeSum.LightBandPrimeSetup.time (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) R (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) (n^k) ≤
      _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget k n := by
  have ht := _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.setup_time_le (_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.maxMod n) (_root_.ThreeSum1960614.Machine.ThreeSum.BandScales.bandSize n) R (_root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n) (_root_.ThreeSum.Scales.primeWindow n) (n^k)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.depth_eq_primeDepth] at ht
  refine ht.trans ?_
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.timeBudget
  apply Nat.add_le_add_left
  calc
    _ ≤ 5*(_root_.ThreeSum.Scales.primeDepth _root_.ThreeSum1960614.Machine.ThreeSum.Scales.radix n+1)*(3*_root_.ThreeSum1960614.Machine.ThreeSum.CostLedger.bandCount n^2+1)*
        (_root_.ThreeSum.LightPrimePool.size (_root_.ThreeSum.Scales.primeWindow n)+1)^2*(3*_root_.ThreeSum1960614.Machine.ThreeSum.ArithmeticStageBounds.perTripleBudget k n) := by
      gcongr
      exact _root_.ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.unit_le_budget k hn
    _ = _ := by ring
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.setup_time_le_budget__implementation_df86a00035) := (@ThreeSum1960614.Machine.ThreeSum.BandPrimeCosts.setup_time_le_budget__implementation_df86a00035)

#print axioms solution
