-- Prove2me | solution 1 for ThreeSum.BandPrimeCosts.setup_time_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:05:52.631581+00:00
-- url     : https://prove2.me/submissions/4cfcc7a5-4cbb-425b-ab7b-cd5640170537

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Theorems.Thm_ThreeSum_BandPrimeCosts_aggregate_time_le
import Theorems.Thm_ThreeSum_ModuloCosts_time_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum.LightModuloCounts
end ThreeSum.LightModuloCounts
namespace ThreeSum.MassScales
end ThreeSum.MassScales
namespace ThreeSum.ModuloCosts
end ThreeSum.ModuloCosts
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.UniformStageBounds
end ThreeSum.UniformStageBounds

section


/-!
# Arbitrary-length interface for the verified multiplication routine

These exact inequalities convert a requested positive coefficient length
to its power-of-two capacity. Polynomial padding preserves the represented
product. The fifth-power bounds include any fixed linear preparation and
folding overhead, so no real-exponent oracle is needed for the time bound.
-/

namespace ThreeSum.KaratsubaInterface

open ThreeSum.Karatsuba ThreeSum.LightKaratsuba Polynomial



theorem le_capacity (p : ℕ) : p ≤ capacity p := Nat.le_pow_clog (by decide) p























































































end ThreeSum.KaratsubaInterface

end

section


/-!
# Uniform bounds for repeated modular-counting calls

A caller may reserve resources for the largest modulus it will use. These
lemmas relate that reservation to the exact costed program contract.
-/

namespace ThreeSum.ModuloRuntime

open LightModuloCounts KaratsubaInterface

theorem capacity_mono {p q : ℕ} (h : p ≤ q) : capacity p ≤ capacity q := by
  exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right 2 h)

theorem karatsuba_time_mono : Monotone LightKaratsuba.time := by
  apply monotone_nat_of_le_succ
  intro k
  rw [LightKaratsuba.time]
  omega

theorem time_mono {p q : ℕ} (h : p ≤ q) (nA nB nC U : ℕ) :
    time p nA nB nC U ≤ time q nA nB nC U := by
  have hc := capacity_mono h
  have hl := Nat.clog_mono_right 2 h
  have ht := karatsuba_time_mono hl
  unfold time LightCapacity.time LightResidueHistogram.time
    LightHistogram.histogramTime LightCyclic.combinedTime
  simp only [Light.fillTime, LightArray.linearTime]
  omega
















































end ThreeSum.ModuloRuntime

end

section


/-!
# Finite arithmetic-operation bounds for the complete counting backend

The only input-size dependence outside the Karatsuba term is the number of
original elements times their remainder bit budget. Histogram initialization,
capacity computation and folding are included in the displayed constant.
-/

namespace ThreeSum.ModuloCosts

open KaratsubaInterface



theorem capacity_le_roundedPower (p : ℕ) : capacity p ≤ roundedPower p :=
  Nat.pow_le_pow_left (by decide) _










































end ThreeSum.ModuloCosts

end

section


/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds

open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology

set_option maxHeartbeats 1000000























theorem bits_le_window_square (n : ℕ) : inputBits n+1 ≤ primeWindow n^2 := by
  have hroot := Nat.lt_succ_sqrt' (inputBits n)
  have hpow : Nat.sqrt (inputBits n)+1 ≤ 2^(Nat.sqrt (inputBits n)+1) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hs := Nat.pow_le_pow_left hpow 2
  unfold primeWindow windowExponent
  simp only [Nat.succ_eq_add_one] at hroot
  omega

theorem remainder_bits_le {n : ℕ} (k : ℕ) (hn : 0 < n) :
    Nat.log 2 (n^k+1)+1 ≤ bitBudget k n := by
  have hp : 0 < n^k := Nat.pow_pos hn
  have hm := Nat.log_mono_right (b := 2) (show n^k+1 ≤ 3*n^k by omega)
  have hl := log2_difference_bound k hn
  rw [Nat.log2_eq_log_two] at hl
  have hw := Nat.mul_le_mul_left (2*(k+2)) (bits_le_window_square n)
  unfold bitBudget
  omega

theorem invocation_le_budget {n p nA nB nC : ℕ} (k : ℕ)
    (hn : 0 < n) (hp : p ≤ maxMod n)
    (ha : nA ≤ bandSize n) (hb : nB ≤ bandSize n) (hc : nC ≤ bandSize n) :
    LightModuloCounts.time p nA nB nC (n^k) ≤ perTripleBudget k n := by
  have ht := ModuloRuntime.time_mono hp nA nB nC (n^k)
  have hbnd := ModuloCosts.time_bound (maxMod n) nA nB nC (bandSize n) (n^k) ha hb hc
  have hm := Nat.mul_le_mul_left (bandSize n) (remainder_bits_le k hn)
  unfold perTripleBudget
  omega

noncomputable section


































































































































end
end ThreeSum.ArithmeticStageBounds

end

section


/-!
# Compute the prescribed common-prime depth without division

The loop compares successive `4*(4*y)^(i+1)` with the radix. It returns
exactly `Nat.log (4*y) (R/4)`, including the zero-depth case. Only local
variables change, and the number of iterations is that logarithm.
-/

namespace ThreeSum.LightBandPrimeDepth

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000














variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}
















































































theorem depth_eq_primeDepth (n : ℕ) :
    depth (Scales.radix n) (Scales.primeWindow n)=Scales.primeDepth Scales.radix n := rfl

end ThreeSum.LightBandPrimeDepth

end

section


/-!
# Charge the executed common-prime setup

The bound includes the generated pool, every aggregate candidate minimum,
all original band-score calls, and the computed chain depth. The size-only
budget uses the same quadratic owner bound as the physical mass theorem.
-/

namespace ThreeSum.BandPrimeCosts

open Scales BandScales CostLedger ArithmeticStageBounds

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000




theorem unit_ge (p g U : ℕ) : 1000 ≤ unit p g U := by unfold unit; omega





















theorem minimum_time_le (p g R s U : ℕ) :
    LightBandPrimeMinimum.time p g R s U ≤ 3*(R+1)*(s+1)^2*unit p g U := by
  have hv : 1000 ≤ (R+1)*(s+1)*unit p g U :=
    (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have hh := aggregate_time_le p g R s U
  calc
    _ = (s+1)*(LightBandWeightedScore.time p g R s U+140) := by
      unfold LightBandPrimeMinimum.time; ring
    _ ≤ (s+1)*(3*((R+1)*(s+1)*unit p g U)) := by
      apply Nat.mul_le_mul_left
      nlinarith
    _ = _ := by ring



theorem core_ge (p g R s U : ℕ) : 1000 ≤ core p g R s U := by
  have hp : 0 < (R+1)*(s+1)^2 := by positivity
  exact (unit_ge p g U).trans (Nat.le_mul_of_pos_left _ hp)

theorem chain_time_le (p g R s U levels : ℕ) :
    LightBandPrimeChain.time p g R s U levels ≤ 4*(levels+1)*core p g R s U := by
  have hm : LightBandPrimeMinimum.time p g R s U ≤ 3*core p g R s U := by
    simpa only [core,Nat.mul_assoc] using minimum_time_le p g R s U
  have hh := Nat.mul_le_mul_left levels (Nat.add_le_add_right hm 140)
  have hc := core_ge p g R s U
  unfold LightBandPrimeChain.time
  nlinarith

theorem setup_time_le (p g R M y U : ℕ) :
    LightBandPrimeSetup.time p g R M y U ≤ LightPrimePool.time y+
      5*(LightBandPrimeDepth.depth M y+1)*(R+1)*(LightPrimePool.size y+1)^2*unit p g U := by
  have hc := chain_time_le p g R (LightPrimePool.size y) U (LightBandPrimeDepth.depth M y)
  have hg := core_ge p g R (LightPrimePool.size y) U
  have hh : LightBandPrimeDepth.time M y+
      LightBandPrimeChain.time p g R (LightPrimePool.size y) U (LightBandPrimeDepth.depth M y)+240 ≤
      5*(LightBandPrimeDepth.depth M y+1)*core p g R (LightPrimePool.size y) U := by
    unfold LightBandPrimeDepth.time
    nlinarith
  unfold LightBandPrimeSetup.time LightBandPrimeConstruction.time
  simp only [core,Nat.mul_assoc] at hh ⊢
  omega














theorem unit_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    unit (maxMod n) (bandSize n) (n^k) ≤ 3*perTripleBudget k n := by
  have hc := invocation_le_budget (p := maxMod n) k hn le_rfl le_rfl le_rfl le_rfl
  have hp := (KaratsubaInterface.le_capacity (maxMod n)).trans (ModuloCosts.capacity_le_roundedPower (maxMod n))
  have hl : Nat.log 2 (maxMod n+1) ≤ maxMod n+1 := Nat.log_le_self _ _
  have hj : LightWeightedScore.jointTime (maxMod n) ≤ perTripleBudget k n := by
    unfold LightWeightedScore.jointTime LightResidues.residueBudget perTripleBudget
    omega
  have hlarge : 1000 ≤ perTripleBudget k n := by unfold perTripleBudget; omega
  unfold unit
  omega





theorem setup_time_le_budget_sourceProof {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightBandPrimeSetup.time (maxMod n) (bandSize n) R (radix n) (primeWindow n) (n^k) ≤
      timeBudget k n := by
  have ht := setup_time_le (maxMod n) (bandSize n) R (radix n) (primeWindow n) (n^k)
  rw [LightBandPrimeDepth.depth_eq_primeDepth] at ht
  refine ht.trans ?_
  unfold timeBudget
  apply Nat.add_le_add_left
  calc
    _ ≤ 5*(primeDepth radix n+1)*(3*bandCount n^2+1)*
        (LightPrimePool.size (primeWindow n)+1)^2*(3*perTripleBudget k n) := by
      gcongr
      exact unit_le_budget k hn
    _ = _ := by ring

end ThreeSum.BandPrimeCosts

end


theorem solution : ∀ {n R : Nat} (k : Nat),
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LE.le.{0} Nat instLENat R
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
            (ThreeSum.CostLedger.bandCount n) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
      @LE.le.{0} Nat instLENat
        (ThreeSum.LightBandPrimeSetup.time (ThreeSum.ArithmeticStageBounds.maxMod n) (ThreeSum.BandScales.bandSize n) R
          (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n)
          (@HPow.hPow.{0, 0, 0} Nat Nat Nat
            (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n k))
        (ThreeSum.BandPrimeCosts.timeBudget k n) := by
  exact @ThreeSum.BandPrimeCosts.setup_time_le_budget_sourceProof

#print axioms solution
