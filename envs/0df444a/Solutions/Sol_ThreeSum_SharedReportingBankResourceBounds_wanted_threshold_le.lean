-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.wanted_threshold_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:09:06.454114+00:00
-- url     : https://prove2.me/submissions/6586922e-2466-4299-a43d-266540b126dc

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle12
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
import Theorems.Thm_ThreeSum_BandRawA_mem_aIndices_iff_owner
import Theorems.Thm_ThreeSum_BandRawA_mem_allProducts
import Theorems.Thm_ThreeSum_BandRawA_owner_weightedFalseCount
import Theorems.Thm_ThreeSum_BandWeightedScore_block_bound
import Theorems.Thm_ThreeSum_LightPrimePool_prefix_increasing
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_representation_cap_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
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
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
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
# The aggregate weighted score of physical band-owner candidates

Each flagged owner contributes the score of its three actual truncated
bands. Owner multiplicities are retained. The contraction and initial bound
therefore apply to the same quadratic catalog that the program scans.
-/

namespace ThreeSum.BandWeightedScore

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
































































theorem partialScore_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) (k : ℕ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    partialScore primes s q nA nB nC g A B C rs k ≤ k*(s*g^3) := by
  calc
    _ ≤ ∑ _i ∈ range k, s*g^3 := sum_le_sum fun i _ => block_bound primes s q nA nB nC g A B C _ hprime hinj
    _ = _ := by simp

theorem score_bound (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j) :
    score primes s q nA nB nC g A B C rs ≤ rs.length*(s*g^3) :=
  partialScore_bound primes s q nA nB nC g A B C rs rs.length hprime hinj


















































end ThreeSum.BandWeightedScore

end

section


/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000



























































theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (ownerProduct nA nB nC g rs s) (ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (mem_ownerProduct hs).mp hx
  have ht' := (mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)
















































theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ t ∈ allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by
  unfold allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst





























end ThreeSum.BandRawA

end

section


/-!
# The aggregate prime score is the exact physical incidence-product score

The executable A catalog supplies the first-coordinate values. Its owner
metadata supplies the B/C slices. Thus the mathematical score summed by
the actual prime selector counts this same domain with all multiplicities.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000







































theorem all_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (allProducts nA nB nC g rs)
      (ModuloCounts.difference (valueAt nA g rs A) B C)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  unfold Arithmetic.weightedFalseCount
  rw [sum_allProducts]
  unfold BandWeightedScore.score BandWeightedScore.partialScore
  apply sum_congr rfl
  intro s hs
  exact owner_weightedFalseCount primes aux q nA nB nC g A B C rs (mem_range.mp hs)














































end ThreeSum.BandRawA

end

section


/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000




















theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))

















@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]













theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩








theorem finite_lift {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    ∃ u ∈ finiteAllProducts nA nB nC g rs, coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact mem_finiteAllProducts.mpr ht
















theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ u ∈ finiteAllProducts nA nB nC g rs, F (coordinates u))=
      ∑ t ∈ allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl














theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs















end ThreeSum.BandRawA

end

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






































theorem prefix_nodup (y i : ℕ) : (scanned y i).Nodup :=
  (prefix_increasing y i).imp (fun h => Nat.ne_of_lt h)






theorem values_nodup (y : ℕ) : (values y).Nodup := prefix_nodup y (3*y)
theorem size_le (y : ℕ) : size y ≤ 3*y := prefix_length_le y (3*y)























theorem prime_spec {y i : ℕ} (hi : i < size y) :
    Nat.Prime (prime y i) ∧ y < prime y i ∧ prime y i ≤ 4*y :=
  mem_values.mp (prime_mem hi)

theorem prime_injective {y i j : ℕ} (hi : i < size y) (hj : j < size y)
    (heq : prime y i = prime y j) : i = j :=
  (List.getD_inj hi hj (values_nodup y)).mp heq









































































variable {lim : Limits} {P : Program} {d : ℕ}
























































































end ThreeSum.LightPrimePool

end

section


/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup

open Light GlobalEncoding BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000




































theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    falseScore primes s q nA nB nC g A B C rs=
      BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}




























































































end ThreeSum.LightDenseSetup

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


























































































































































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Size-only magnitudes for physical wanted indices

The left index includes the lift and the retained A-incidence position.
The right index selects an original output record, including its occurrence
identity. Neither bound depends on the magnitude of the input integers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales GlobalEncoding LocalCoverBounds OutputDecodeRecords
open SharedReportingBankLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000



theorem input_le_magnitude (n : ℕ) : n ≤ magnitude n := by
  have hn : n ≤ 2^(inputBits n+1) := by
    simpa only [inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hn.trans (Nat.pow_le_pow_right (by decide) (by omega))




























































































end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Explicit finite scale bounds for reporter words and the dense counter -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light GlobalEncoding LocalCoverBounds SharedReportingBankLayout
open ReportingHostWantedLayout

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000











































































































theorem wanted_prime_pool_le (n : ℕ) : LightPrimePool.size (primeWindow n)≤3*magnitude n := by
  have hs := Nat.sqrt_le_self (inputBits n)
  have hw : primeWindow n≤magnitude n :=
    Nat.pow_le_pow_right (by decide) (by dsimp only [windowExponent]; omega)
  exact (LightPrimePool.size_le _).trans (Nat.mul_le_mul_left 3 hw)

theorem wanted_threshold_le_sourceProof {n nA nB nC q : ℕ}
    (A B C : ℕ→ℤ) (rs : List BandCandidateRows.Record) (hrs : rs.length≤3*n^2) :
    representationCap (half n) (blocks n)*
      LightDenseSetup.falseScore (LightPrimePool.prime (primeWindow n))
        (LightPrimePool.size (primeWindow n)) q nA nB nC (BandScales.bandSize n) A B C rs≤
      9*(magnitude n)^8 := by
  rw [LightDenseSetup.falseScore_eq]
  have hs := BandWeightedScore.score_bound (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)) q nA nB nC (BandScales.bandSize n) A B C rs
    (fun i hi => (LightPrimePool.prime_spec hi).1) (fun i hi j hj => LightPrimePool.prime_injective hi hj)
  have hr := hrs.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (input_le_magnitude n) 2))
  have hh := Nat.mul_le_mul (wanted_representation_cap_le n)
    (Nat.mul_le_mul hr (Nat.mul_le_mul (wanted_prime_pool_le n)
      (Nat.pow_le_pow_left (band_le_magnitude n) 3)))
  calc
    _ ≤ representationCap (half n) (blocks n)*(rs.length*
        (LightPrimePool.size (primeWindow n)*(BandScales.bandSize n)^3)) := Nat.mul_le_mul_left _ hs
    _ ≤ (magnitude n)^2*((3*(magnitude n)^2)*((3*magnitude n)*(magnitude n)^3)) := hh
    _ = _ := by ring

end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ {n nA nB nC q : Nat} (A B C : Nat → Int) (rs : List.{0} ThreeSum.BandCandidateRows.Record),
  @LE.le.{0} Nat instLENat (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid))) n
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))) →
    @LE.le.{0} Nat instLENat
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (ThreeSum.GlobalEncoding.representationCap (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n))
        (ThreeSum.LightDenseSetup.falseScore (ThreeSum.LightPrimePool.prime (ThreeSum.Scales.primeWindow n))
          (ThreeSum.LightPrimePool.size (ThreeSum.Scales.primeWindow n)) q nA nB nC (ThreeSum.BandScales.bandSize n) A B
          C rs))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))) := by
  exact @ThreeSum.SharedReportingBankResourceBounds.wanted_threshold_le_sourceProof

#print axioms solution
