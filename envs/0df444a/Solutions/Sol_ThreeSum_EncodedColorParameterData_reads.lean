-- Prove2me | solution 1 for ThreeSum.EncodedColorParameterData.reads
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:09.586329+00:00
-- url     : https://prove2.me/submissions/f4ce8f3e-807a-4e5d-915e-494e8af3e136

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales

section


/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology

















































































noncomputable section















































































































































































































































































































































theorem muZero_eq_twice_half (n : ℕ) : muZero n = 2 * microHalf (inputBits n) := rfl











































































































































































































































































































































































































































































































end

end ThreeSum.Scales

end

section


/-!
# Executing global powers and rounded band sizes

This routine consumes the already computed local output count, local prime,
block count, and total inner size. All global powers, the square-root
rounding, and the final ceiling division are actual Light computations.
The square-root loop and quotient loop are included in the stated time.
-/

namespace ThreeSum.LightGlobalSizes

set_option maxHeartbeats 1000000

open Light LocalCoverBounds








































variable {lim : Limits} {P : Program} {d : ℕ}






















































































































theorem localCount_pow (n : ℕ) :
    localCount n ^ Scales.blockCount (Scales.inputBits n) = Scales.typedOutputs n := by
  have hwidth : 256*Scales.muZero n = 512*Scales.microHalf (Scales.inputBits n) := by
    rw [Scales.muZero_eq_twice_half]
    ring
  unfold Scales.typedOutputs
  rw [hwidth,Scales.muZero_eq_twice_half]
  rfl

theorem values_scales (n : ℕ) :
    values (localCount n) (Scales.localRadix n) (Scales.blockCount (Scales.inputBits n)) (Scales.mu n) =
      [(Scales.typedOutputs n : ℤ),Scales.radix n,BandScales.bandRoot n,
        BandScales.bandDivisor n,BandScales.bandSize n] := by
  simp only [values,root,localCount_pow,divisor,band,numerator,
    Scales.radix,BandScales.bandRoot,BandScales.bandDivisor,BandScales.bandSize,Nat.ceilDiv_eq_add_pred_div]

end ThreeSum.LightGlobalSizes

end

section


/-! # Physical control reads for one selected-color workspace -/

namespace ThreeSum.EncodedColorParameterData

open Light Scales BandScales

theorem reads_sourceProof {μ : ℕ → ℤ} {params n : ℕ} (H : Seg μ params (LightParameterInit.values n)) :
    μ params=(inputBits n : ℤ) ∧ μ (params+1)=(microHalf (inputBits n) : ℤ) ∧
    μ (params+3)=(blockCount (inputBits n) : ℤ) ∧ μ (params+4)=(mu n : ℤ) ∧
    μ (params+14)=(radix n : ℤ) ∧ μ (params+17)=(bandSize n : ℤ) ∧
    μ (params+18)=(primeWindow n : ℤ) := by
  have h (i : ℕ) (hi : i < 19) := H.getD (i := i)
    (by simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,
      LightLocalCounts.values,LightGlobalSizes.values] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [LightParameterInit.values,LightScales.values] using h 0 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 1 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 3 (by omega)
  · simpa [LightParameterInit.values,LightScales.values] using h 4 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 14 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 17 (by omega)
  · simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values_scales] using h 18 (by omega)















end ThreeSum.EncodedColorParameterData

end


theorem solution : ∀ {μ : Nat → Int} {params n : Nat},
  Light.Seg μ params (ThreeSum.LightParameterInit.values n) →
    And (@Eq.{1} Int (μ params) (@Nat.cast.{0} Int instNatCastInt (ThreeSum.Scales.inputBits n)))
      (And
        (@Eq.{1} Int
          (μ
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
              (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))))
        (And
          (@Eq.{1} Int
            (μ
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
                (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
            (@Nat.cast.{0} Int instNatCastInt (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n))))
          (And
            (@Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
                  (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.Scales.mu n)))
            (And
              (@Eq.{1} Int
                (μ
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
                    (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))
                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.Scales.radix n)))
              (And
                (@Eq.{1} Int
                  (μ
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
                      (@OfNat.ofNat.{0} Nat (nat_lit 17) (instOfNatNat (nat_lit 17)))))
                  (@Nat.cast.{0} Int instNatCastInt (ThreeSum.BandScales.bandSize n)))
                (@Eq.{1} Int
                  (μ
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) params
                      (@OfNat.ofNat.{0} Nat (nat_lit 18) (instOfNatNat (nat_lit 18)))))
                  (@Nat.cast.{0} Int instNatCastInt (ThreeSum.Scales.primeWindow n)))))))) := by
  exact @ThreeSum.EncodedColorParameterData.reads_sourceProof

#print axioms solution
