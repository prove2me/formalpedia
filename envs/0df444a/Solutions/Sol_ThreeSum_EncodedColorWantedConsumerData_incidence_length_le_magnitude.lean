-- Prove2me | solution 1 for ThreeSum.EncodedColorWantedConsumerData.incidence_length_le_magnitude
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:39:55.405733+00:00
-- url     : https://prove2.me/submissions/ba1950e0-6e2a-4c7b-9433-d784ebbdc483

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle15
import Definitions.Def_ThreeSum1962Source_Bundle16
import Definitions.Def_ThreeSum1962Source_Bundle17
import Definitions.Def_ThreeSum1962Source_Bundle18
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_components


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.ColorClassLists
end ThreeSum.ColorClassLists
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.EncodedColorLayout
end ThreeSum.EncodedColorLayout
namespace ThreeSum.EncodedColorNormalizedData
end ThreeSum.EncodedColorNormalizedData
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightClassFilter
end ThreeSum.LightClassFilter
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
namespace ThreeSum.ThreeSumWantedHostData
end ThreeSum.ThreeSumWantedHostData
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

section


/-!
# The exact physical band-owner record order

There is one four-cell record for every owner-table cell, in BC, AB, AC
rectangle order. A zero flag is a lookup miss. Successful records retain
their physical owner slot even when several owners produce the same triple.
-/

namespace ThreeSum.BandCandidateRows

open BandEnumeration

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000



















































theorem rect_length (m n : ℕ) (F : ℕ → ℕ → Record) : (rect m n F).length=m*n := by
  simp [rect,List.length_flatMap]

theorem records_length (A B C : Family) :
    (records A B C).length=LightBandEnumeration.count A.size B.size C.size := by
  simp only [records,List.length_append,rect_length,LightBandEnumeration.count]
  omega


















































































































































end ThreeSum.BandCandidateRows

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

theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega

































theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega


















































end ThreeSum.BandPartition

end

section


/-!
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000





























theorem row_length (n g owner : ℕ) (r : Record) :
    (row n g owner r).length=if r.flag=1 then bandLength n g r.a else 0 := by
  unfold row
  split_ifs <;> simp

theorem row_length_le (n g owner : ℕ) (r : Record) : (row n g owner r).length ≤ g := by
  rw [row_length]
  split_ifs
  · exact BandPartition.length_le n g r.a
  · omega










theorem firstRows_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    firstRows n g rs (i+1)=firstRows n g rs i++row n g i (rs.getD i default) := by
  simp only [firstRows,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

@[simp] theorem count_zero (n g : ℕ) (rs : List Record) : count n g rs 0=0 := rfl

theorem count_succ (n g : ℕ) (rs : List Record) (i : ℕ) :
    count n g rs (i+1)=count n g rs i+(row n g i (rs.getD i default)).length := by
  simp only [count,firstRows_succ,List.length_append]







theorem count_bound (n g : ℕ) (rs : List Record) (i : ℕ) : count n g rs i ≤ g*i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [count_succ]
    have hh := row_length_le n g i (rs.getD i default)
    nlinarith

theorem items_length_le (n g : ℕ) (rs : List Record) : (items n g rs).length ≤ g*rs.length :=
  count_bound n g rs rs.length

























































































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
# Stable extraction of one color class from the original signed array

The program reads stored colors and original values. It writes a length
header followed by exactly the selected values, optionally negated. Repeated
values are preserved; deduplication belongs to the later normalization pass.
-/

namespace ThreeSum.LightClassFilter

open Light

set_option maxHeartbeats 1200000












theorem items_length_le (x : ℕ → ℤ) (color : ℕ → ℕ) (want : ℕ) (scale : ℤ) (n : ℕ) :
    (items x color want scale n).length ≤ n := by
  simpa only [items,List.length_map,List.length_range] using
    List.length_filter_le (p := fun i => decide (color i = want)) (l := List.range n)

























variable {lim : Limits} {P : Program} {d : ℕ}























































































end ThreeSum.LightClassFilter

end

section


/-!
# Exact original-position semantics of the constructed color-class lists

The machine keeps repeated values within a class and negates the third
class. The list membership witnesses are original positions. Any binary
width large enough for the indices suffices for the deterministic family.
-/

namespace ThreeSum.ColorClassLists

open LightClassFilter




































theorem length_classList_le {n W : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) : (classList p x c scale).length ≤ n :=
  items_length_le ..



































































end ThreeSum.ColorClassLists

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


/-! # Actual finite budgets of the retained common-prime stage -/

namespace ThreeSum.EncodedColorPrimeCosts

open Light Scales BandScales CostLedger ArithmeticStageBounds
















theorem count_mono {nA nB nC nA' nB' nC' g : ℕ} (ha : nA ≤ nA') (hb : nB ≤ nB') (hc : nC ≤ nC') :
    LightEncodedColorPrime.count nA nB nC g ≤ LightEncodedColorPrime.count nA' nB' nC' g := by
  have a := BandPartition.size_mono (g := g) ha
  have b := BandPartition.size_mono (g := g) hb
  have c := BandPartition.size_mono (g := g) hc
  unfold LightEncodedColorPrime.count
  exact Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul b c) (Nat.mul_le_mul a b)) (Nat.mul_le_mul a c)






























































end ThreeSum.EncodedColorPrimeCosts

end

section


/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData

open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout
















theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (sortedRecords A B C g hg hsA hsB hsC).length ≤ ColorBandBounds.count n g := by
  have h := EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : LightEncodedColorPrime.count n n n g=ColorBandBounds.count n g := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [sortedRecords, BandCandidateRows.records_length]
  exact h






























end ThreeSum.EncodedColorNormalizedData

end

section


/-!
# Actual encoding-output masses fit the uniform reporting budgets

Both inequalities come from the retained pipeline payload. The wanted
count includes all physical A occurrences and all three lifts; the false
score uses the very common modulus selected from the original normalized
arrays. No input-dependent counting or prime-quality premise is assumed.
The explicit numerical divisor premise is discharged eventually, uniformly
before the input arrays are quantified.
-/

namespace ThreeSum.ThreeSumColorBudgets

open Light Scales BandScales CostLedger GlobalEncoding LocalCoverBounds
open ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000


















variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (length_classList_le color x 2 (-1))⟩


























































































open Filter













end ThreeSum.ThreeSumColorBudgets

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
# The actual retained inputs of the physical wanted consumer

These are projections and finite bounds for the same normalized witnesses
retained by the selected-color pipeline. Physical A incidences preserve
their owner labels even when their integer values are equal.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000















variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}





























theorem incidence_length_eq (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (config free n A B C hsA hsB hsC).N=
      (BandRawA.items A.length (bandSize n) (records n A B C hsA hsB hsC)).length :=
  BandRawA.values_length ..

theorem incidence_length_le_records (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (config free n A B C hsA hsB hsC).N≤bandSize n*recordCount n A B C hsA hsB hsC := by
  rw [incidence_length_eq]
  exact BandRawA.items_length_le ..

theorem record_count_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    recordCount n A B C hsA hsB hsC≤ColorBandBounds.count n (bandSize n) := by
  obtain ⟨ha,hb,hc⟩ := ThreeSumColorBudgets.normalized_lengths H
  exact EncodedColorNormalizedData.records_length_le ha hb hc

theorem size_le_magnitude (n : ℕ) : n≤SharedReportingBankResourceBounds.magnitude n := by
  have hp : n≤2^(inputBits n+1) := by
    simpa [inputBits,Nat.log2_eq_log_two,Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1<2) n).le
  exact hp.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem incidence_length_le_magnitude_sourceProof
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (config free n A B C hsA hsB hsC).N≤3*(SharedReportingBankResourceBounds.magnitude n)^3 := by
  have hr := record_count_le H
  have hc : ColorBandBounds.count n (bandSize n)≤3*n^2 :=
    Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (BandPartition.size_le n (bandSize n)) 2)
  have hg := SharedReportingBankResourceBounds.band_le_magnitude n
  have hn := size_le_magnitude n
  calc
    _ ≤ bandSize n*recordCount n A B C hsA hsB hsC := incidence_length_le_records ..
    _ ≤ SharedReportingBankResourceBounds.magnitude n*(3*n^2) := Nat.mul_le_mul hg (hr.trans hc)
    _ ≤ SharedReportingBankResourceBounds.magnitude n*(3*(SharedReportingBankResourceBounds.magnitude n)^2) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hn 2))
    _ = _ := by ring



























end ThreeSum.EncodedColorWantedConsumerData

end


theorem solution : ∀ {μ : Nat → Int} {free n : Nat}
  {color :
    ThreeSum.Coloring.Parameter
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (ThreeSum.Scales.inputBits n)
        (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))}
  {x : Fin n → Int} {A B C : List.{0} Int}
  {hsA : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) A}
  {hsB : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) B}
  {hsC : @List.Pairwise.{0} Int (fun (x1 x2 : Int) => @LT.lt.{0} Int Int.instLTInt x1 x2) C}
  (H : ThreeSum.EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC),
  @LE.le.{0} Nat instLENat (ThreeSum.ThreeSumWantedHostData.config free n A B C hsA hsB hsC).N
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))) := by
  exact @ThreeSum.EncodedColorWantedConsumerData.incidence_length_le_magnitude_sourceProof

#print axioms solution
