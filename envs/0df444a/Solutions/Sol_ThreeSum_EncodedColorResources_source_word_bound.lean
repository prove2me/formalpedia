-- Prove2me | solution 1 for ThreeSum.EncodedColorResources.source_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:17:42.662444+00:00
-- url     : https://prove2.me/submissions/f5ac4ec3-1612-4868-af46-a58c58e0ae9a

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
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
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
import Theorems.Thm_ThreeSum_EncodedColorResources_source_controls_word_le
import Theorems.Thm_ThreeSum_LightLocalCoverMagnitude_bounds
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

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

theorem local_bounds (n : ℕ) : LightLocalCoverMagnitude.Bounds (half n) (scale n) := by
  have hm : LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
    unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
    exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))
  have hs := hm.trans (scale_bounds n).2.2.2.1
  have H := LightLocalCoverMagnitude.bounds (half n)
  exact ⟨H.positive.trans hs,H.width.trans hs,H.vertices.trans hs,H.prime.trans hs,
    H.cap.trans hs,H.candidates.trans hs,H.rounds.trans hs,H.decodePower.trans hs,H.maskPower.trans hs⟩

















theorem powers (n : ℕ) : 2^(width n+1) ≤ scale n ∧
    LightBlockSourceCatalog.count (half n) (blocks n) ≤ scale n ∧
    localPrime (half n)^(blocks n)*localPrime (half n) ≤ scale n ∧
    2^(blocks n) ≤ scale n := by
  have H := SharedReportingBankResourceBounds.components n
  have hm := (scale_bounds n).2.2.1
  refine ⟨H.widthPower.trans hm,H.occurrence.trans hm,H.primePower.trans hm,?_⟩
  have htwo : (2 : ℕ) ≤ 2^(512*half n)+1 := by have hh := Nat.two_pow_pos (512*half n); omega
  exact (Nat.pow_le_pow_left htwo (blocks n)).trans (H.radixPower.trans hm)

theorem modulus_le (n : ℕ) : BlockSourceEncoding.modulus (half n) (blocks n) ≤ scale n := by
  exact (Nat.le_mul_of_pos_right _ (localPrime_pos (half n))).trans (powers n).2.2.1

theorem endpoint_le (n : ℕ) : LightBlockSourceBuild.endpointBound (half n) (blocks n) ≤ (scale n)^2 := by
  have hw : width n ≤ scale n := by have hh := (dimensions n).1; omega
  have hh := Nat.mul_le_mul hw (powers n).2.2.1
  simpa only [LightBlockSourceBuild.endpointBound,width,BlockSourceEncoding.modulus,pow_two] using hh
















































noncomputable section


















end
end ThreeSum.EncodedColorResources

end

section


/-! # Finite space and word bounds for the actual retained source constructors -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open SubsetAddress CostLedger TrimScales

set_option maxHeartbeats 2600000
set_option maxRecDepth 13000












































































































































theorem retained_source_word_le (n : ℕ) : LightBlockSourceRetainedHost.word n n (half n) (blocks n) ≤ 50*(scale n)^2 := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hW := (dimensions n).1
  have H := local_bounds n
  have hL := H.width
  have hP := H.prime
  have hcap := H.cap
  have hlocal := H.maskPower
  have hpow := (powers n).1
  have hPP := (powers n).2.2.1
  have hmod := modulus_le n
  have hE := endpoint_le n
  have hV : (512*half n).choose (half n) ≤ scale n := by
    have hp0 : 2^(512*half n) ≤ scale n :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (by omega : 2^(512*half n+1) ≤ scale n)
    exact (Nat.choose_le_two_pow _ _).trans hp0
  have hpow0 : 2^(width n) ≤ scale n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hpow
  have hcoeff := Nat.mul_le_mul hPP hP
  have hglobal := Nat.mul_le_mul hW hPP
  have hrow := Nat.mul_le_mul hL hP
  have hLP := Nat.mul_le_mul (show 512*half n ≤ scale n by omega) (show localPrime (half n) ≤ scale n by omega)
  have hwp := Nat.mul_le_mul hW hpow
  have hnp := Nat.mul_le_mul hpow0 (show n ≤ scale n by omega)
  unfold LightBlockSourceRetainedHost.word LightSourcePreparation.word LightBlockSourceHashes.word
    LightBlockCoefficients.word LightOneHot.word LightSourceMaskFlags.word LightSourceRowFlag.word
    LightSourceRowScan.word LightSourceRetainedStages.word
  rw [pow_succ (localPrime (half n)) (blocks n)]
  dsimp only [width] at hW hpow hglobal hwp hnp
  nlinarith only [hb,hn,hW,hL,hP,hcap,hpow,hmod,hE,hV,hcoeff,hglobal,hrow,hLP,hwp,hnp]

theorem source_word_bound_sourceProof (n U : ℕ) :
    SourceFiniteCosts.word n (maxMod n) U (radix n) ≤ 200*(scale n)^3+4*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hJ := (dimensions n).2.1
  have hg := (dimensions n).2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hP := (scale_bounds n).2.2.2.2.1
  have hmod := modulus_le n
  have hS := (local_bounds n).rounds
  have hocc := (powers n).2.1
  have hcontrols := source_controls_word_le n
  have hretained := retained_source_word_le n
  have hbank : LightSourceBandBanks.word n n (half n) (blocks n) ≤ 60*(scale n)^2 := by
    unfold LightSourceBandBanks.word LightSourceBandBankStep.word LightOutputDecodeDigits.word
    apply max_le <;> nlinarith only [hb,hn,hJ,hS,hocc,hretained]
  unfold SourceFiniteCosts.word LightSourceControlsHost.word LightSourceBandHost.word
    LightSourceBandPair.word LightSourceBandStep.word LightSourceResidues.word
  change max (LightSourceControls.word (half n) (blocks n) (mu n))
    (max (max (4*U+8*maxMod n+4*radix n+4*BlockSourceEncoding.modulus (half n) (blocks n)+32+n+bandSize n+2)
      (4*U+8*maxMod n+4*radix n+4*BlockSourceEncoding.modulus (half n) (blocks n)+32+n+bandSize n+2)+16)
      (LightSourceBandBanks.word n n (half n) (blocks n))) ≤ _
  simp only [max_self]
  apply max_le
  · omega
  · apply max_le <;> nlinarith only [hb,hn,hg,hM,hP,hmod,hbank]

end ThreeSum.EncodedColorResources

end


theorem solution : ∀ (n U : Nat),
  @LE.le.{0} Nat instLENat
    (ThreeSum.SourceFiniteCosts.word n (ThreeSum.ArithmeticStageBounds.maxMod n) U (ThreeSum.Scales.radix n))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 200) (instOfNatNat (nat_lit 200)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.EncodedColorResources.scale n) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))) U)) := by
  exact @ThreeSum.EncodedColorResources.source_word_bound_sourceProof

#print axioms solution
