-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.scaled_word_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:08:45.615688+00:00
-- url     : https://prove2.me/submissions/292b232e-2d21-45d5-992f-88adda58acb8

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_source_span_le_magnitude


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

section


/-!
# The executable band size and its exact exponent

The band numerator is the integer ceiling of the square root of the actual
typed output count. The denominator is `2^(mu/20)`. Since the block schedule
has `20 ∣ mu`, the denominator exponent has no divisibility error.
-/

namespace ThreeSum.BandScales

open Filter Real ThreeSum.Scales
open scoped Topology











theorem typedOutputs_pos (n : ℕ) : 0 < typedOutputs n := by
  unfold typedOutputs
  exact Nat.pow_pos (Nat.choose_pos (by omega))



























noncomputable section

































































































































end

end ThreeSum.BandScales

end

section


/-!
# Exact sharing of source transforms and the encoder ledger

Source stages are indexed by a source band and an occurrence vector. The
output subset and the three-valued A lift do not enter the source function.
Compact table and zeta charges below match the existing `encoderCount`
without introducing a factor for all complete global outputs.
-/

namespace ThreeSum.BlockSourceSharing

open BlockEncoding GlobalEncoding BlockIndexedQuery SubsetAddress
open Scales TrimScales CostLedger StageBounds






































theorem width_eq (n : ℕ) :
    blockCount (inputBits n)*(512*microHalf (inputBits n)) = 256*mu n := by
  unfold mu totalSize microSize microHalf
  ring

































































end ThreeSum.BlockSourceSharing

end

section


/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts

open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds

theorem choose_mul_le (L K N M : ℕ) : L.choose K*N.choose M ≤ (L+N).choose (K+M) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun ij : ℕ×ℕ => L.choose ij.1*N.choose ij.2)
    (fun _ _ => Nat.zero_le _) (by simp : (K,M) ∈ Finset.antidiagonal (K+M))

theorem choose_pow_le (L K J : ℕ) : (L.choose K)^J ≤ (J*L).choose (J*K) := by
  induction J with
  | zero => simp
  | succ J ih =>
    calc
      _ = (L.choose K)^J*L.choose K := pow_succ _ _
      _ ≤ (J*L).choose (J*K)*L.choose K := Nat.mul_le_mul_right _ ih
      _ ≤ (J*L+L).choose (J*K+K) := choose_mul_le _ _ _ _
      _ = _ := by simp only [Nat.succ_mul]

theorem typedOutputs_le_fullOutputs (n : ℕ) : typedOutputs n ≤ fullOutputs n := by
  have h := choose_pow_le (256*muZero n) (muZero n) (blockCount (inputBits n))
  have hwidth : blockCount (inputBits n)*(256*muZero n)=256*mu n := by
    unfold mu muZero totalSize
    ring
  have hcut : blockCount (inputBits n)*muZero n=mu n := rfl
  rw [hwidth,hcut] at h
  exact h





































theorem bandSize_le_fullOutputs (n : ℕ) : bandSize n ≤ fullOutputs n := by
  have hb : bandSize n ≤ bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := bandDivisor n) (bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (bandDivisor_pos n)
  have hr : bandRoot n ≤ typedOutputs n := by
    have hs := Nat.sqrt_le_self (typedOutputs n-1)
    have hp := typedOutputs_pos n
    unfold bandRoot rootCeiling
    omega
  exact hb.trans (hr.trans (typedOutputs_le_fullOutputs n))











































































end ThreeSum.SourceBandCosts

end

section


/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000























































































theorem band_le_magnitude (n : ℕ) : BandScales.bandSize n ≤ magnitude n := by
  have hB := SourceBandCosts.bandSize_le_fullOutputs n
  have hfull : TrimScales.fullOutputs n ≤ 2^(width (half n) (blocks n)) := by
    rw [show width (half n) (blocks n)=256*mu n from BlockSourceSharing.width_eq n]
    exact Nat.choose_le_two_pow _ _
  exact (hB.trans hfull).trans ((Nat.pow_le_pow_right (by decide) (by omega : width (half n) (blocks n) ≤
    width (half n) (blocks n)+1)).trans (components n).widthPower)

theorem prefix_storage_le_magnitude (n : ℕ) :
    prefixStorage (half n) (blocks n) ≤ (magnitude n+1)^2 := by
  have H := components n
  have hmul := Nat.mul_le_mul (H.levelsBound.trans (Nat.le_succ _)) (Nat.add_le_add_right H.prefixBound 1)
  simpa only [prefixStorage,pow_two] using hmul







































































































theorem scaled_word_le_sourceProof (n : ℕ) : scaledWord n ≤ envelope n := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hJ := H.blocksBound
  have hK := H.levelsBound
  have hN := H.prefixBound
  have hC := H.occurrence
  have hP := H.localPower
  have hE := H.pairsPower
  have hWP := H.widthPower
  have hIP := H.indexPower
  have hD := H.depthWord
  have hG := band_le_magnitude n
  have hS := prefix_storage_le_magnitude n
  have hspan := source_span_le_magnitude n
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hWP
  have hlocal : 2^(512*half n) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hP
  have hv := Nat.mul_le_mul hlocal H.radixPower
  have hkeyMul := Nat.mul_le_mul hlocal hv
  have hkeys : LightRadixKeys.word (2^(512*half n)) (2^(512*half n)) (blocks n) ≤
      (magnitude n)^3+2*magnitude n+1 := by
    unfold LightRadixKeys.word LightRadixRows.word
    nlinarith
  have hindexMul := Nat.mul_le_mul (Nat.pow_le_pow_left hpower 2) (Nat.add_le_add_right hIP 1)
  have hindex : LightReportingSortedCatalog.word (width (half n) (blocks n))
      (2^(2*width (half n) (blocks n))) ≤ (magnitude n)^2*(magnitude n+1)+3*magnitude n+2 := by
    unfold LightReportingSortedCatalog.word LightReportingPackKeys.word
    omega
  have hwidth := Nat.mul_le_mul hW hWP
  have hv1 := Nat.mul_le_mul hpower hG
  have hv2 := Nat.mul_le_mul hv1 hv1
  have hv3 := Nat.mul_le_mul hpower hv2
  have hcontrol := Nat.mul_le_mul_right n hC
  have hswitch := Nat.pow_le_pow_left H.switchBase 64
  let R := (magnitude n+1)^5*(n+1)^2
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hp : 1 ≤ (magnitude n+1)^5 := Nat.one_le_pow _ _ (by omega)
  have dominates {e : ℕ} (he : e ≤ 5) : (magnitude n+1)^e ≤ R :=
    (Nat.pow_le_pow_right (by omega) he).trans (Nat.le_mul_of_pos_right _ hn)
  have smaller {e : ℕ} (he : e ≤ 5) : (magnitude n)^e ≤ R :=
    (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (dominates he)
  have oneR : 1 ≤ R := by simpa only [pow_zero] using dominates (e := 0) (by decide)
  have magR : magnitude n ≤ R := by simpa only [pow_one] using smaller (e := 1) (by decide)
  have nquad : n ≤ (n+1)^2 := by nlinarith only [Nat.zero_le n]
  have nR : n ≤ R := nquad.trans (Nat.le_mul_of_pos_left _ hp)
  have mnR : magnitude n*n ≤ R := Nat.mul_le_mul
    ((Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)) nquad
  have controlR := hcontrol.trans mnR
  have storageR := hS.trans (dominates (e := 2) (by decide))
  have spanR := hspan.trans (Nat.mul_le_mul_left 100 (dominates (e := 3) (by decide)))
  have cubeR := smaller (e := 3) (by decide)
  have keysR : LightRadixKeys.word (2^(512*half n)) (2^(512*half n)) (blocks n) ≤ 4*R := by omega
  have indexProductR : (magnitude n)^2*(magnitude n+1) ≤ R := by
    calc
      _ ≤ (magnitude n+1)^2*(magnitude n+1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ _) 2)
      _ = (magnitude n+1)^3 := by ring
      _ ≤ R := dominates (by decide)
  have indexR : LightReportingSortedCatalog.word (width (half n) (blocks n))
      (2^(2*width (half n) (blocks n))) ≤ 6*R := by omega
  have widthR : (width (half n) (blocks n)+1)*2^(width (half n) (blocks n)+1) ≤ R := by
    exact hwidth.trans (by simpa only [pow_two] using smaller (e := 2) (by decide))
  have valuesR : 2^(width (half n) (blocks n))*
      ((2^(width (half n) (blocks n))*BandScales.bandSize n)*
       (2^(width (half n) (blocks n))*BandScales.bandSize n)) ≤ R := by
    exact hv3.trans (by simpa only [show magnitude n*((magnitude n*magnitude n)*(magnitude n*magnitude n))=
      (magnitude n)^5 by ring] using smaller (e := 5) (by decide))
  unfold scaledWord word envelope
  apply Nat.add_le_add _ hswitch
  rw [show polynomialPart n=5000*R by dsimp [R,polynomialPart]; ring]
  unfold control stateWord
  omega

end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ (n : Nat),
  @LE.le.{0} Nat instLENat (ThreeSum.SharedReportingBankResourceBounds.scaledWord n)
    (ThreeSum.SharedReportingBankResourceBounds.envelope n) := by
  exact @ThreeSum.SharedReportingBankResourceBounds.scaled_word_le_sourceProof

#print axioms solution
