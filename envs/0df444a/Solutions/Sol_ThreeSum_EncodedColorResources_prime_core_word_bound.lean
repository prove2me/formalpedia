-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.prime_core_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:07:19.798552+00:00
-- url     : https://prove2.me/submissions/814cdf25-c12c-4664-a854-b9ff8c673be7

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.Sublists
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
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
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_EncodedColorResources_dimensions
import Theorems.Thm_ThreeSum_KaratsubaInterface_capacity_lt_twice


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
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.HierarchyScales
end ThreeSum.HierarchyScales
namespace ThreeSum.KaratsubaInterface
end ThreeSum.KaratsubaInterface
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
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



















theorem maxMod_pos (n : ℕ) : 0 < maxMod n := by
  unfold maxMod
  exact Nat.mul_pos (radix_pos n) (Nat.pow_pos (by have := primeWindow_ge_two n; omega))






























noncomputable section


































































































































end
end ThreeSum.ArithmeticStageBounds

end

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition





theorem size_le (n g : ℕ) : size n g ≤ n := by
  unfold size
  split_ifs with h
  · omega
  · have hdiv := Nat.div_le_self (n-1) g
    omega
































































































end ThreeSum.BandPartition

end

section


/-!
# Executing the candidate prime pool

This fixed program scans the integers in `(y,4*y]`, invokes the concrete
trial-division procedure, and writes every prime exactly once in increasing
order. The returned length and written array are the exact candidate pool
used by the contraction and auxiliary-weight theorems.
-/

namespace ThreeSum.LightPrimePool

open Light

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000






theorem prefix_length_le (y i : ℕ) : (scanned y i).length ≤ i := by
  induction i with
  | zero => simp [scanned]
  | succ i ih =>
      unfold scanned
      split
      · simp only [List.length_append,List.length_singleton]
        omega
      · omega















































theorem size_le (y : ℕ) : size y ≤ 3*y := prefix_length_le y (3*y)







































































































variable {lim : Limits} {P : Program} {d : ℕ}
























































































end ThreeSum.LightPrimePool

end

section


/-!
# Exact resource formulas for the original-input band and incidence program

These formulas use the existing selected-color layout without changing any
address or procedure. The physical BC, AB, AC owner records and the packed
value, owner, and sorted-position arrays are all included in the extent.
-/

namespace ThreeSum.LightBandRawAResources

open Light EncodedColorLayout

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000






















theorem count_le (n g : ℕ) : ColorBandBounds.count n g ≤ 3*n^2 :=
  Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n g) 2)






















end ThreeSum.LightBandRawAResources

end

section


/-! # A proved polynomial scale for the selected-color program's dimensions -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open Filter

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000








theorem scale_bounds (n : ℕ) : 100 ≤ scale n ∧ n+1 ≤ scale n ∧
    SharedReportingBankResourceBounds.magnitude n ≤ scale n ∧ localEnvelope n ≤ scale n ∧
    maxMod n ≤ scale n ∧ primeWindow n ≤ scale n := by
  unfold scale
  omega



























































































noncomputable section


















end
end ThreeSum.EncodedColorResources

end

section


/-! # Affine storage and finite word bounds for the unchanged prime host -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open EncodedColorLayout KaratsubaInterface

set_option maxHeartbeats 2400000
set_option maxRecDepth 13000

theorem count_le (n : ℕ) : ColorBandBounds.count n (bandSize n) ≤ 3*(scale n)^2 := by
  have hn : n ≤ scale n := by have h := (scale_bounds n).2.1; omega
  exact (LightBandRawAResources.count_le n (bandSize n)).trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))

























































theorem capacity_bound (n : ℕ) : capacity (maxMod n) ≤ 2*scale n :=
  (capacity_lt_twice (maxMod_pos n)).le.trans (Nat.mul_le_mul_left 2 (scale_bounds n).2.2.2.2.1)

theorem prime_core_word_bound_sourceProof (n U : ℕ) :
    LightEncodedColorPrimeCore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (radix n) (primeWindow n) U ≤ 5000*(scale n)^6+4*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hg := (dimensions n).2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hP := (scale_bounds n).2.2.2.2.1
  have hy := (scale_bounds n).2.2.2.2.2
  have hR := count_le n
  have hs := (LightPrimePool.size_le (primeWindow n)).trans (Nat.mul_le_mul_left 3 hy)
  have hcap := capacity_bound n
  have hg2 : bandSize n+1 ≤ 2*scale n := by omega
  have hkar : LightKaratsuba.wordBound (capacity (maxMod n)) (bandSize n) ≤ 4096*(scale n)^5 := by
    unfold LightKaratsuba.wordBound
    calc
      _ ≤ 128*(2*scale n)^3*(2*scale n)^2 := by gcongr
      _ = _ := by ring
  have hg3 := Nat.pow_le_pow_left hg 3
  have hsg := Nat.mul_le_mul (show LightPrimePool.size (primeWindow n)+1 ≤ 3*scale n+1 by omega) hg3
  have hrg := Nat.mul_le_mul hR (Nat.mul_le_mul hs hg3)
  have hdprod := Nat.mul_le_mul hy (Nat.add_le_add_right hM 4)
  have hp16 : scale n ≤ (scale n)^6 := Nat.le_self_pow (by decide) _
  have hp26 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 2 ≤ 6)
  have hp36 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 3 ≤ 6)
  have hp46 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 4 ≤ 6)
  have hp56 := Nat.pow_le_pow_right (by omega : 1 ≤ scale n) (by decide : 5 ≤ 6)
  have hweighted : LightBandWeightedScore.word (maxMod n) n n n (bandSize n)
      (ColorBandBounds.count n (bandSize n)) (LightPrimePool.size (primeWindow n)) U ≤ 5000*(scale n)^6+4*U := by
    unfold LightBandWeightedScore.word LightBandWeightedScoreCell.word LightWeightedScore.word LightModuloCounts.word
    nlinarith only [hb,hn,hg,hP,hR,hkar,hg3,hsg,hrg,hp16,hp26,hp36,hp46,hp56]
  unfold LightEncodedColorPrimeCore.word
  apply max_le
  · unfold LightBandPrimeDepth.word
    nlinarith only [hb,hM,hdprod,hp16,hp26]
  · apply max_le
    · unfold LightPrimePool.word
      nlinarith only [hb,hy,hp16]
    · exact hweighted































































end ThreeSum.EncodedColorResources

end


theorem solution : ∀ (n U : Nat),
  @LE.le.{0} Nat instLENat
    (ThreeSum.LightEncodedColorPrimeCore.word (ThreeSum.ArithmeticStageBounds.maxMod n) n n n
      (ThreeSum.BandScales.bandSize n) (ThreeSum.ColorBandBounds.count n (ThreeSum.BandScales.bandSize n))
      (ThreeSum.Scales.radix n) (ThreeSum.Scales.primeWindow n) U)
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 5000) (instOfNatNat (nat_lit 5000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.EncodedColorResources.scale n) (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) U)) := by
  exact @ThreeSum.EncodedColorResources.prime_core_word_bound_sourceProof

#print axioms solution
