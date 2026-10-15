-- Prove2me | solution 1 for ThreeSum.EncodedColorCoverData.source_controls
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:43:08.600979+00:00
-- url     : https://prove2.me/submissions/20d5c42c-a6fe-4fd3-89b9-8f02a66ca7d2

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle14
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


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.SourceFiniteInputs
end ThreeSum.SourceFiniteInputs

section


/-! # Read source controls from the actually constructed local-cover header -/

namespace ThreeSum.EncodedColorCoverData

open Light GlobalEncoding LocalCoverBounds SourceFiniteInputs





theorem source_controls_sourceProof {μ : ℕ → ℤ} {free h J : ℕ} (H : LightCoverKeyData.Stored μ free h J) :
    μ (free+6)=(localPrime h : ℤ) ∧ μ (free+7)=(localBucketCap h : ℤ) ∧
    μ (free+8)=(512*h : ℤ) ∧ μ (free+10)=(scheduleSize h : ℤ) ∧
    μ (free+12)=(maps free h : ℤ) ∧ μ (free+13)=(candidates free h : ℤ) ∧
    μ (free+14)=(leftCounts free h : ℤ) ∧ μ (free+15)=(rightCounts free h : ℤ) := by
  have h (i : ℕ) (hi : i < 20) := H.header.getD (i := i)
    (by simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals
    first
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 6 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 7 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 8 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 10 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 12 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 13 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 14 (by omega)
    | simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
        LightLocalCoverMetadata.values,maps,candidates,leftCounts,rightCounts] using h 15 (by omega)

end ThreeSum.EncodedColorCoverData

end


theorem solution : ∀ {μ : Nat → Int} {free h J : Nat},
  ThreeSum.LightCoverKeyData.Stored μ free h J →
    And
      (@Eq.{1} Int
        (μ
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
            (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))))
        (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localPrime h)))
      (And
        (@Eq.{1} Int
          (μ
            (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
              (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))))
          (@Nat.cast.{0} Int instNatCastInt (ThreeSum.LocalCoverBounds.localBucketCap h)))
        (And
          (@Eq.{1} Int
            (μ
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8)))))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (@OfNat.ofNat.{0} Int (nat_lit 512) (@instOfNat (nat_lit 512))) (@Nat.cast.{0} Int instNatCastInt h)))
          (And
            (@Eq.{1} Int
              (μ
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                  (@OfNat.ofNat.{0} Nat (nat_lit 10) (instOfNatNat (nat_lit 10)))))
              (@Nat.cast.{0} Int instNatCastInt (ThreeSum.GlobalEncoding.scheduleSize h)))
            (And
              (@Eq.{1} Int
                (μ
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                    (@OfNat.ofNat.{0} Nat (nat_lit 12) (instOfNatNat (nat_lit 12)))))
                (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceFiniteInputs.maps free h)))
              (And
                (@Eq.{1} Int
                  (μ
                    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                      (@OfNat.ofNat.{0} Nat (nat_lit 13) (instOfNatNat (nat_lit 13)))))
                  (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceFiniteInputs.candidates free h)))
                (And
                  (@Eq.{1} Int
                    (μ
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                        (@OfNat.ofNat.{0} Nat (nat_lit 14) (instOfNatNat (nat_lit 14)))))
                    (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceFiniteInputs.leftCounts free h)))
                  (@Eq.{1} Int
                    (μ
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) free
                        (@OfNat.ofNat.{0} Nat (nat_lit 15) (instOfNatNat (nat_lit 15)))))
                    (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SourceFiniteInputs.rightCounts free h))))))))) := by
  exact @ThreeSum.EncodedColorCoverData.source_controls_sourceProof

#print axioms solution
