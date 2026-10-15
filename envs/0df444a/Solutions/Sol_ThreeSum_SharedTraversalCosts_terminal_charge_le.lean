-- Prove2me | solution 1 for ThreeSum.SharedTraversalCosts.terminal_charge_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:19:51.70567+00:00
-- url     : https://prove2.me/submissions/db2d6f15-5292-4ad3-b968-10f82577c9bf

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
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
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
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
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
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
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
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
import Mathlib.Logic.Equiv.Fin.Basic
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_SubsetAddress_enumerationWork_bound


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawPrefixCounts
end ThreeSum.RawPrefixCounts
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.SourceFlagProduct
end ThreeSum.SourceFlagProduct
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






















































































































































theorem buildTime_bound (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightPascal

end

section


/-!
# Output-sensitive subset-layer enumeration in the benchmark language

The recursive routine writes into consecutive output cells. Empty layers
return immediately; a zero-cardinality layer emits one mask. The two
recursive children share the output buffer and write adjacent, disjoint
segments. No ambient Boolean cube is scanned and no output list is copied.
-/

namespace ThreeSum.LightSubsetEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}












































theorem time_bound (L k : ℕ) :
    time L k ≤ 150*((4*L+1)*L.choose k+1) := by
  exact Nat.mul_le_mul_left 150 (enumerationWork_bound L k)



























































































































































end ThreeSum.LightSubsetEnumeration

end

section


/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}























































































































































theorem time_bound (W : ℕ) : time W ≤ 500*(W+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightQueryWeights

end

section


/-!
# A complete output-sensitive subset enumerator inside an arbitrary query mask

The routine constructs its own compact coordinate weights, then invokes
the existing recursion on the number of selected coordinates. Every emitted
word is already a global mask; no ambient layer or Boolean cube is scanned.
-/

namespace ThreeSum.LightQueryEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates

variable {lim : Limits} {P : Program}












































































theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by
  have hbuild := LightQueryWeights.time_bound W
  have he := LightSubsetEnumeration.time_bound c t
  unfold time
  have hpoly : (4*c+1)*c.choose t+1 ≤ 4*(W+1)^2*(c.choose t+1) := by
    have hW : W+1 ≤ (W+1)^2 := by nlinarith
    nlinarith
  nlinarith [Nat.one_le_pow' 2 W]

end ThreeSum.LightQueryEnumeration

end

section


/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks

variable {lim : Limits} {P : Program}





























































































































































theorem time_bound {W c h : ℕ} (hc : c ≤ W) :
    time W c h ≤ 1600*(W+1)^2*(c.choose h+1) := by
  have he := LightQueryEnumeration.time_bound (t := h) hc
  have hpow : 1 ≤ (W+1)^2 := by nlinarith
  unfold time LightReportingAffine.time
  nlinarith

end ThreeSum.LightBlockChildren

end

section


/-!
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}
















































































































































































































theorem time_bound (J L : ℕ) : time J L ≤ 300*(J+1)*(L+1) := by
  unfold time roundTime LightScaleArray.time powTableTime
  nlinarith

end ThreeSum.LightBlockCoefficients

end

section


/-!
# Evaluating a whole list of one-hot mask hashes

This wrapper builds the powers table itself, hashes each stored mask, and
writes the raw nonnegative values. It is shared by the local-cover matrix
construction and input-source encoding. The cost is linear in the number
of masks times their width; no evaluation oracle is assumed.
-/

namespace ThreeSum.LightMaskHashes

open Light LightSubsetAddress

set_option maxHeartbeats 1000000



















variable {lim : Limits} {P : Program} {d : ℕ}









































































































theorem time_bound (L n : ℕ) : time L n ≤ 300*(L+1)*(n+1) := by
  unfold time powTableTime LightOneHot.time
  nlinarith

end ThreeSum.LightMaskHashes

end

section


/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes

open Light BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000





























variable {lim : Limits} {P : Program} {d : ℕ}



















































































































































theorem time_bound (J L n : ℕ) :
    time J L n ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+200 := by
  have hc := LightBlockCoefficients.time_bound J L
  have hh := LightMaskHashes.time_bound (J*L) n
  unfold time
  nlinarith

end ThreeSum.LightBlockSourceHashes

end

section


/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase































variable {lim : Limits} {P : Program} {d : ℕ}






















































































theorem time_bound (L : ℕ) : time L ≤ 300*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskBits

end

section


/-! # Actual Pascal lookup for reporting child and terminal candidate counts -/

namespace ThreeSum.LightReportingBinomial

open Light LightPascal

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000










variable {lim : Limits}


























theorem time_bound (n : ℕ) : time n≤1100*(n+1)^2 := by
  have hh := LightPascal.buildTime_bound n
  have hp : 1≤(n+1)^2 := by
    have hp0 : 0<(n+1)^2 := by positivity
    omega
  unfold time
  nlinarith

end ThreeSum.LightReportingBinomial

end

section


/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks

open Light Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open QueryCoordinates ReportingHostTerminalChoices ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000























































variable {lim : Limits} {d : ℕ}








































theorem time_bound (h J k : ℕ) :
    time h J k≤1600*(J*(512*h)+1)^2*(2^((J-k)*(2*h))+1) := by
  have hc : (J-k)*(2*h)≤J*(512*h) :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  exact (LightBlockChildren.time_bound (h := (J-k)*h) hc).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.choose_le_two_pow _ _) 1))

end ThreeSum.LightReportingTerminalMasks

end

section


/-!
# Constructing both independent trimming flags for one block row

The program counts and hashes the actual Boolean row, reduces both local
hashes, reads the selected map's retained bucket tables, and independently
tests the two endpoint buckets. The cardinality test is performed for both
orientations, with no disjoint-pair or shared trimming assumption.
-/

namespace ThreeSum.LightSourceRowFlag

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000




























variable {lim : Limits} {P : Program} {d : ℕ}






















































































































theorem time_bound (L U : ℕ) :
    time L U ≤ 150*L+464*(Nat.log 2 (L*U+1)+1) := by
  unfold time LightSourceRowScan.time LightResidues.residueBudget LightSourceFlagTest.time
  nlinarith

end ThreeSum.LightSourceRowFlag

end

section


/-!
# Independent endpoint trimming across all selected blocks

The loop reads each occurrence index and its exact selected-candidate index,
then calls the concrete row flag constructor on the corresponding map and
retained bucket tables. The product of the independent Boolean flags is
written in each orientation. Input Boolean rows and tables are preserved.
-/

namespace ThreeSum.LightSourceTrim

open Light SourceFlagProduct

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000























































variable {lim : Limits} {P : Program} {d : ℕ}





































































































































































theorem time_bound (J L U : ℕ) :
    time J L U ≤ J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+100 := by
  have hh := LightSourceRowFlag.time_bound L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left J (Nat.add_le_add_right hh 250)) 100

end ThreeSum.LightSourceTrim

end

section


/-!
# Constructing independent endpoint flags directly from a global mask

The fixed program creates its own powers and Boolean coordinate row, then
performs the actual selected-block trimming scan. There is no Boolean-bit or
trim-flag oracle in the contract.
-/

namespace ThreeSum.LightSourceMaskFlags

open Light SourceFlagProduct

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000



























variable {lim : Limits} {P : Program} {d : ℕ}






































































































theorem time_bound (J L U : ℕ) :
    time J L U ≤ 300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+200 := by
  have hb := LightMaskBits.time_bound (J*L)
  have ht := LightSourceTrim.time_bound J L U
  unfold time
  omega

end ThreeSum.LightSourceMaskFlags

end

section


/-!
# Constructing contiguous arrays of independent source flags

The actual loop reads the already enumerated global masks. For each one it
constructs both independent flags from selected maps and retained bucket
counts, then writes the two orientations in separate adjacent arrays. Powers,
Boolean coordinates and local arithmetic scratch are reused across masks.
-/

namespace ThreeSum.LightSourceFlagArray

open Light SourceFlagProduct

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000




































variable {lim : Limits} {P : Program} {d : ℕ}














































































































































theorem time_bound (n J L U : ℕ) :
    time n J L U ≤ n*(300*(J*L+1)^2+
      J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+10 := by
  have hh := LightSourceMaskFlags.time_bound J L U
  unfold time
  exact Nat.add_le_add_right (Nat.mul_le_mul_left n (by omega)) 10

end ThreeSum.LightSourceFlagArray

end

section


/-!
# Actual endpoint and independent-flag preparation from stored selected maps

The host constructs radix coefficient rows, both raw endpoint arrays, and
both independent trim-flag arrays. All four arrays are retained for the
original-input histogram/source-stage constructors.
-/

namespace ThreeSum.LightSourcePreparation

open Light BlockCoefficientRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000
























variable {lim : Limits} {P : Program} {d : ℕ}
























































































































theorem time_bound (n J L U : ℕ) :
    time n J L U ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+
      n*(300*(J*L+1)^2+J*(150*L+464*(Nat.log 2 (L*U+1)+1)+250)+400)+410 := by
  have hh := LightBlockSourceHashes.time_bound J L n
  have hf := LightSourceFlagArray.time_bound n J L U
  unfold time
  omega

end ThreeSum.LightSourcePreparation

end

section


/-!
# Local parameter construction fits the uniform subpolynomial budget

These bounds apply to the actual operational contracts, including the
primality scans and integer division. The deliberately loose envelope is
only used for a microblock whose half-size is a cube root of `log n`.
-/

namespace ThreeSum.LocalParameterBounds

open LocalCoverBounds

set_option maxHeartbeats 1000000




theorem pow_pos (e : ℕ) : 1 ≤ (2 : ℕ)^e := Nat.pos_iff_ne_zero.mpr (pow_ne_zero _ (by decide))

theorem threshold_bound (h : ℕ) : localThreshold h ≤ 2^(514*h) := by
  calc
    localThreshold h ≤ 2^(512*h)*2^(2*h) :=
      Nat.mul_le_mul_right _ (Nat.choose_le_two_pow _ _)
    _ = 2^(514*h) := by rw [← pow_add]; congr 1 <;> omega




theorem root_bound (h : ℕ) : rootCeiling (localThreshold h) ≤ 2*2^(514*h) := by
  have hs := Nat.sqrt_le_self (localThreshold h-1)
  have ht := threshold_bound h
  have hp := pow_pos (514*h)
  unfold rootCeiling
  omega

theorem prime_bound (h : ℕ) : localPrime h ≤ 2^(514*h+2) := by
  have hp := (selectedPrime_spec (localThreshold h)).2.2
  have hr := root_bound h
  change localPrime h ≤ _ at hp
  rw [pow_add]
  norm_num
  omega

























































































































































end ThreeSum.LocalParameterBounds

end

section


/-!
# Polynomial overhead of the actual traversal operations

All logarithmic residue costs are bounded before the binomial work terms
are charged. This prevents an endpoint magnitude from being used as a
running-time bound. The final scalar overhead is polynomial in the block
dimensions and will therefore have exponent zero at the prescribed scales.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Light LocalCoverBounds LightBlockQuery ReportingHostLevelData
open SubsetAddress
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000




theorem size_bounds (h J : ℕ) :
    1 ≤ size h J ∧ J+1 ≤ size h J ∧ 512*h+1 ≤ size h J ∧
      width h J+1 ≤ size h J ∧
      1026*h+4 ≤ size h J ∧
      J*(512*h)+(514*h+2)*(J+1)+2 ≤ size h J := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> simp only [size,width] <;> nlinarith

theorem log_local_le (h : ℕ) : Nat.log 2 (512*h*localPrime h+1)+1 ≤ 1026*h+4 := by
  have hp := LocalParameterBounds.prime_bound h
  have hw : 512*h ≤ 2^(512*h) := (Nat.lt_two_pow_self (n := 512*h)).le
  have hh : 512*h*localPrime h ≤ 2^(1026*h+2) := by
    calc
      _ ≤ 2^(512*h)*2^(514*h+2) := Nat.mul_le_mul hw hp
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hh' : 512*h*localPrime h+1 ≤ 2^(1026*h+3) := by
    have hz := Nat.two_pow_pos (1026*h+2)
    rw [show 1026*h+3=(1026*h+2)+1 by omega,pow_succ]
    omega
  have hl := Nat.log_mono_right (b := 2) hh'
  rw [Nat.log_pow (by decide)] at hl
  omega

theorem log_endpoint_le (h J : ℕ) :
    Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+1 ≤
      J*(512*h)+(514*h+2)*(J+1)+2 := by
  let W := J*(512*h)
  let E := W+(514*h+2)*(J+1)
  have hpow : localPrime h^J*localPrime h ≤ 2^((514*h+2)*(J+1)) := by
    rw [← pow_succ]
    exact (Nat.pow_le_pow_left (LocalParameterBounds.prime_bound h) _).trans_eq
      (pow_mul _ _ _).symm
  have hw : W ≤ 2^W := (Nat.lt_two_pow_self (n := W)).le
  have he : LightBlockSourceBuild.endpointBound h J ≤ 2^E := by
    unfold LightBlockSourceBuild.endpointBound
    change W*(localPrime h^J*localPrime h) ≤ 2^E
    exact (Nat.mul_le_mul hw hpow).trans_eq (pow_add 2 W ((514*h+2)*(J+1))).symm
  have he' : LightBlockSourceBuild.endpointBound h J+1 ≤ 2^(E+1) := by
    have hz := Nat.two_pow_pos E
    rw [pow_succ]
    omega
  have hl := Nat.log_mono_right (b := 2) he'
  rw [Nat.log_pow (by decide)] at hl
  dsimp [E,W] at hl
  omega

theorem residue_le_size (h J : ℕ) :
    LightResidues.residueBudget (LightBlockSourceBuild.endpointBound h J) ≤ 77*size h J := by
  have hb := size_bounds h J
  have hl := log_endpoint_le h J
  unfold LightResidues.residueBudget
  omega

theorem preparation_time_le (h J n : ℕ) :
    LightSourcePreparation.time n J (512*h) (localPrime h) ≤
      4000*(size h J)^2*(n+1) := by
  let B := size h J
  have hb := size_bounds h J
  have hlog := (log_local_le h).trans hb.2.2.2.2.1
  have hJ : J+1 ≤ B := hb.2.1
  have hL : 512*h+1 ≤ B := hb.2.2.1
  have hW : J*(512*h)+1 ≤ B := hb.2.2.2.1
  have hp : 1 ≤ B := hb.1
  have hB : B ≤ B^2 := Nat.le_self_pow (by decide) _
  have hbase := Nat.mul_le_mul hJ hL
  have hrow : J*(150*(512*h)+464*(Nat.log 2 (512*h*localPrime h+1)+1)+250) ≤
      864*B^2 := by
    calc
      _ ≤ B*(864*B) := Nat.mul_le_mul (by omega : J ≤ B) (by omega)
      _ = _ := by ring
  have hmain : 300*(J*(512*h)+1)^2+
      J*(150*(512*h)+464*(Nat.log 2 (512*h*localPrime h+1)+1)+250)+400 ≤ 1564*B^2 := by
    have hs := Nat.pow_le_pow_left hW 2
    nlinarith
  have htime := LightSourcePreparation.time_bound n J (512*h) (localPrime h)
  have hfirst : 300*(J+1)*(512*h+1) ≤ 300*B^2 := by nlinarith [hbase]
  have hsecond := Nat.mul_le_mul_right (n+1) (show 600*(J*(512*h)+1) ≤ 600*B^2 by omega)
  have hthird := Nat.mul_le_mul_left n hmain
  change LightSourcePreparation.time n J (512*h) (localPrime h) ≤ 4000*B^2*(n+1)
  nlinarith

theorem terminal_charge_le_sourceProof (h J K : ℕ) :
    ReportingHostTerminalFrontier.charge h J K+240 ≤
      31000*(size h J)^2*2^((J-K)*(2*h)) := by
  let B := size h J
  let T := 2^((J-K)*(2*h))
  have hb := size_bounds h J
  have hp : 1 ≤ B := hb.1
  have ht : 1 ≤ T := Nat.two_pow_pos _
  have hB : B ≤ B^2 := Nat.le_self_pow (by decide) _
  have hc : LightReportingTerminalMasks.count h J K ≤ T := Nat.choose_le_two_pow _ _
  have hr : (J-K)*(2*h)+1 ≤ B := by
    have hs := Nat.mul_le_mul (Nat.sub_le J K) (by omega : 2*h ≤ 512*h)
    have hw := hb.2.2.2.1
    change J*(512*h)+1 ≤ B at hw
    omega
  have hbin := (LightReportingBinomial.time_bound ((J-K)*(2*h))).trans
    (Nat.mul_le_mul_left 1100 (Nat.pow_le_pow_left hr 2))
  have hbinT := hbin.trans (Nat.le_mul_of_pos_right _ ht)
  have hmask := LightReportingTerminalMasks.time_bound h J K
  have hmaskT : LightReportingTerminalMasks.time h J K ≤ 3200*B^2*T := by
    calc
      _ ≤ 1600*B^2*(2*T) := hmask.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left 1600 (Nat.pow_le_pow_left hb.2.2.2.1 2)) (by change T+1 ≤ 2*T; omega))
      _ = _ := by ring
  have hprep := preparation_time_le h J (LightReportingTerminalMasks.count h J K)
  have hprepT : LightReportingTerminalPreparation.time h J (LightReportingTerminalMasks.count h J K) ≤
      16800*B^2*T := by
    have hm := hprep.trans (Nat.mul_le_mul_left (4000*B^2) (show
      LightReportingTerminalMasks.count h J K+1 ≤ 2*T by omega))
    unfold LightReportingTerminalPreparation.time
    nlinarith [Nat.mul_le_mul (Nat.one_le_pow 2 B hp) ht]
  have hres := residue_le_size h J
  have hresT : (2*LightResidues.residueBudget (LightBlockSourceBuild.endpointBound h J)+1300)*T ≤
      1454*B^2*T := Nat.mul_le_mul_right T (by nlinarith)
  have hconstant : 2070 ≤ 2070*B^2*T := by
    have hh := Nat.mul_le_mul (Nat.one_le_pow 2 B hp) ht
    nlinarith
  unfold ReportingHostTerminalFrontier.charge
  change LightReportingBinomial.time ((J-K)*(2*h))+LightReportingTerminalMasks.time h J K+
    LightReportingTerminalPreparation.time h J (LightReportingTerminalMasks.count h J K)+
    (2*LightResidues.residueBudget (LightBlockSourceBuild.endpointBound h J)+1300)*T+1830+240 ≤
      31000*B^2*T
  nlinarith only [hbinT,hmaskT,hprepT,hresT,hconstant]

































































end ThreeSum.SharedTraversalCosts

end


theorem solution : ∀ (h J K : Nat),
  @LE.le.{0} Nat instLENat
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (ThreeSum.ReportingHostTerminalFrontier.charge h J K)
      (@OfNat.ofNat.{0} Nat (nat_lit 240) (instOfNatNat (nat_lit 240))))
    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 31000) (instOfNatNat (nat_lit 31000)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedTraversalCosts.size h J) (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@HSub.hSub.{0, 0, 0} Nat Nat Nat (@instHSub.{0} Nat instSubNat) J K)
          (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) h)))) := by
  exact @ThreeSum.SharedTraversalCosts.terminal_charge_le_sourceProof

#print axioms solution
