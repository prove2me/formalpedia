-- Prove2me | solution 1 for ThreeSum.SharedReportingBankCosts.host_time_le
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:17:37.15979+00:00
-- url     : https://prove2.me/submissions/02145f64-610e-44c2-afc7-869e23ab0179

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
import Theorems.Thm_ThreeSum_SharedReportingCosts_time_le_boxes


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.ArithmeticStageBounds
end ThreeSum.ArithmeticStageBounds
namespace ThreeSum.BandScales
end ThreeSum.BandScales
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockSourceSharing
end ThreeSum.BlockSourceSharing
namespace ThreeSum.CostLedger
end ThreeSum.CostLedger
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.ReportingHostPrefixCatalog
end ThreeSum.ReportingHostPrefixCatalog
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingCosts
end ThreeSum.SharedReportingCosts
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.Switch
end ThreeSum.Switch
namespace ThreeSum.TrimScales
end ThreeSum.TrimScales

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition












theorem size_mono {n m g : ℕ} (h : n ≤ m) : size n g ≤ size m g := by
  by_cases hn : n = 0
  · simp [size,hn]
  · have hm : m ≠ 0 := by omega
    have hd := Nat.div_le_div_right (c := g) (show n-1 ≤ m-1 by omega)
    simp only [size,if_neg hn,if_neg hm]
    omega
























































































end ThreeSum.BandPartition

end

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
# A complete subset-rank program, including table construction

This fixed program constructs both lookup tables in scratch and then ranks
one valid mask. Its cost is quadratic in the bit width. The faster cached
rank contract remains available separately, but no supplied table correctness
assumption appears in the fixed-program result below.
-/

namespace ThreeSum.LightSubsetSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}
















































































theorem time_bound (L : ℕ) : time L ≤ 1200*(L+1)^2 := by
  have hb := buildTime_bound L
  unfold time powTableTime rankTime
  nlinarith

end ThreeSum.LightSubsetSetup

end

section


/-!
# Computing the compact downset size

The program builds a Pascal table, scans all preceding layers, and adds
the final binomial coefficient. The table stride used by the transform
is therefore computed by an actual fixed program.
-/

namespace ThreeSum.LightDownsetSize

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}



















































































theorem time_bound (L : ℕ) : time L ≤ 1400*(L+1)^2 := by
  have hh := LightSubsetSetup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time LightSubsetOffset.time
  nlinarith

end ThreeSum.LightDownsetSize

end

section


/-!
# Exact natural quotient by a small counting loop

This helper is used for size parameters whose numerator is logarithmic in
the original input length. Its time is linear in the quotient, explicitly
charged below. A zero divisor returns zero, matching natural division.
-/

namespace ThreeSum.LightSmallDivide

open Light

variable {lim : Limits} {P : Program} {d : ℕ}






































































theorem time_bound (a b : ℕ) : time a b ≤ 20*a+40 := by
  have h := Nat.div_le_self a b
  unfold time
  omega

end ThreeSum.LightSmallDivide

end

section


/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0





































noncomputable section








































































































































theorem actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * blockCount (inputBits n)) 20
  unfold terminalDepth at hj
  omega




























































end
end ThreeSum.Switch

end

section


/-!
# Actual finite hierarchy counts

These are the binomial counts used by the concrete microblock hierarchy.
Every prefix partition is included.  The integer switch and its rounding
allowance are applied before any asymptotic estimate is made.  The counts
in this module are combinatorial work counts; the implementation's operation
counts, raw wanted incidences, and false-mass bounds are separate interfaces.
-/

namespace ThreeSum.CostLedger

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch
open scoped Topology BigOperators

set_option maxHeartbeats 400000






















theorem bandCount_mul_bounds (n : ℕ) :
    n ≤ BandScales.bandSize n * bandCount n ∧
      BandScales.bandSize n * bandCount n < n + BandScales.bandSize n := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := BandScales.bandSize n) (b := n)
      (c := bandCount n) (BandScales.bandSize_pos n)).mp le_rfl
  · have h := Nat.div_mul_le_self (n + BandScales.bandSize n - 1) (BandScales.bandSize n)
    simp only [bandCount, Nat.ceilDiv_eq_add_pred_div]
    rw [Nat.mul_comm (BandScales.bandSize n)]
    have hpos := BandScales.bandSize_pos n
    omega

theorem microOutputs_pos (n : ℕ) : 0 < microOutputs n :=
  Nat.choose_pos (by omega)

theorem microPartitions_pos (n : ℕ) : 0 < microPartitions n :=
  Nat.choose_pos (Nat.div_le_self _ _)

theorem prefixChoices_pos (n j : ℕ) : 0 < prefixChoices n j :=
  Nat.pow_pos (Nat.mul_pos (microOutputs_pos n) (microPartitions_pos n))

theorem suffixBoxes_pos (n j : ℕ) : 0 < suffixBoxes n j :=
  Nat.choose_pos (by omega)

theorem prefixBoxes_pos (n j : ℕ) : 0 < prefixBoxes n j :=
  Nat.mul_pos (prefixChoices_pos n j) (suffixBoxes_pos n j)

noncomputable section

















































































































































end
end ThreeSum.CostLedger

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































theorem occurrence_card (h J : ℕ) : Fintype.card (Occurrences h J) = scheduleSize h^J := by
  simp only [Occurrences,Occurrence,Fintype.card_fun,Fintype.card_fin]

theorem occurrence_card_eq_scheduleCount (n : ℕ) :
    Fintype.card (Occurrences (microHalf (inputBits n)) (blockCount (inputBits n))) = scheduleCount n := by
  rw [occurrence_card,scheduleCount,replicatedHalf,localLength,scheduleSize_eq_length]






































































end ThreeSum.BlockSourceSharing

end

section


/-!
# Exact shared-bank dimensions and charge of the actual catalog

There are two stage families for each original band and occurrence vector.
The decoder and bank-loop overhead are included. Neither the number of
complete output subsets nor the three-valued query lift multiplies this
construction.
-/

namespace ThreeSum.BlockSourceCatalogCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout

theorem count_eq_scheduleCount (n : ℕ) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)) =
      scheduleCount n := by
  unfold LightBlockSourceCatalog.count
  rw [← occurrence_card,occurrence_card_eq_scheduleCount]






























































































end ThreeSum.BlockSourceCatalogCosts

end

section


/-!
# Actual initialization of the integer block schedule

The fixed program computes all initial size parameters from the input
length. It uses the benchmark's proved logarithm, ceiling cube-root and
ceiling-half loops, with exact rounding bridges below. Division is used
only through an actual counting routine on the logarithmic numerator.
-/

namespace ThreeSum.LightScales

open Light ThreeSum.Scales

variable {lim : Limits} {P : Program}














theorem blockCount_le (m : ℕ) : blockCount m ≤ 20*m :=
  Nat.mul_le_mul_left 20 (Nat.div_le_self m (100*microSize m))

theorem totalSize_le_self (m : ℕ) : totalSize m ≤ m := by
  have h := totalSize_upper m
  omega






























































































































































end ThreeSum.LightScales

end

section


/-! # Compute the two local combinatorial counts from an actual Pascal table -/

namespace ThreeSum.LightSharedReportingCounts

open Light LightPascal LightSubsetAddress SubsetAddress SharedReportingBankLayout

set_option maxHeartbeats 1700000
set_option maxRecDepth 9000


























































































theorem time_bound (h : ℕ) : time h ≤ 1500*(512*h+1)^2 := by
  have hb := buildTime_bound (512*h)
  unfold time
  nlinarith [Nat.one_le_pow' 2 (512*h)]

end ThreeSum.LightSharedReportingCounts

end

section


/-! # Actual computation of the terminal reporting depth -/

namespace ThreeSum.LightSwitchDepth

open Light










variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}























theorem time_bound (J : ℕ) : time J ≤ 260*J+90 := by
  have hh := LightSmallDivide.time_bound (13*J) 20
  unfold time
  omega

end ThreeSum.LightSwitchDepth

end

section


/-!
# Charge the complete shared reporting catalog constructor

The actual prefix constructor enumerates the local balanced pairs even at
level zero. That additive local cost is included explicitly and bounded by
the existing local-search factor. Prefix generation, suffix tables and the
sorted physical lookup index are all charged in the complete bound below.
-/

namespace ThreeSum.SharedReportingCosts

open Scales CostLedger ReportingHostPrefixCatalog

set_option maxHeartbeats 1700000
set_option maxRecDepth 10000
























































































theorem terminal_le_blocks (n : ℕ) : Switch.terminalDepth n ≤ blocks n := by
  have hh := Switch.actual_depth_condition (n := n) (le_refl (Switch.terminalDepth n))
  change 20*Switch.terminalDepth n ≤ 13*blocks n at hh
  omega























end ThreeSum.SharedReportingCosts

end

section


/-! # Uniform finite and exponent bounds for the actual switch controls -/

namespace ThreeSum.LightSwitchCosts

open Scales StageBounds ArithmeticStageBounds Filter
open scoped Topology







theorem residual_le_bits (n j : ℕ) : Switch.residualSize n j ≤ inputBits n := by
  calc
    _ ≤ blockCount (inputBits n)*muZero n :=
      Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ ≤ inputBits n := LightScales.totalSize_le_self (inputBits n)

theorem time_le_budget (n j : ℕ) :
    LightSwitch.time (Switch.residualSize n j) ≤ timeBudget n := by
  have hh := residual_le_bits n j
  unfold LightSwitch.time timeBudget
  omega

theorem depth_time_le_budget (n : ℕ) :
    LightSwitchDepth.time (blockCount (inputBits n)) ≤ depthBudget n := by
  have hh := LightSwitchDepth.time_bound (blockCount (inputBits n))
  have hJ := LightScales.blockCount_le (inputBits n)
  unfold depthBudget
  omega

































noncomputable section


























end
end ThreeSum.LightSwitchCosts

end

section


/-! # Finite charge of the actual original-band histogram and bucket catalog -/

namespace ThreeSum.SourceBandCosts

open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds








































































































theorem size_le_bandCount {N n : ℕ} (hN : N ≤ n) : BandPartition.size N (bandSize n) ≤ bandCount n := by
  apply (BandPartition.size_mono hN).trans
  by_cases hn : n=0
  · simp [hn,BandPartition.size]
  · have hg := bandSize_pos n
    have hb := (bandCount_mul_bounds n).1
    have hb' : n ≤ bandCount n*bandSize n := by simpa only [Nat.mul_comm] using hb
    have hd : (n-1)/bandSize n < bandCount n :=
      (Nat.div_lt_iff_lt_mul hg).mpr (by omega)
    simp only [BandPartition.size,if_neg hn]
    omega































end ThreeSum.SourceBandCosts

end

section


/-!
# Charge the executed shared catalog bank, including every surrounding loop

The exact sum of level costs is preserved. Actual switch evaluation,
downset sizing, address arithmetic, row iteration, and the one-time depth
and Pascal initializers add only a factor of exponent zero to the existing
shared-box ledger. The bank is indexed by occurrence and two bands alone.
-/

namespace ThreeSum.SharedReportingBankCosts

open Scales Parameters StageBounds ArithmeticStageBounds CostLedger Filter
open SharedReportingCosts
open scoped Topology

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000









theorem residual_eq (n k : ℕ) :
    SharedReportingBankLevels.residual (half n) (blocks n) k=Switch.residualSize n k := by
  unfold SharedReportingBankLevels.residual half blocks Switch.residualSize muZero microSize microHalf
  ring

theorem cut_eq (n k : ℕ) :
    SharedReportingBankLevels.boxCut (half n) (blocks n) k=
      Switch.residualSize n k-Switch.actualSwitch n k := by
  unfold SharedReportingBankLevels.boxCut SharedReportingBankLevels.switch
  rw [residual_eq]
  rfl

theorem levels_eq (n : ℕ) : SharedReportingBankHeader.levels (blocks n)=Switch.terminalDepth n+1 := rfl

theorem round_time_le {n k : ℕ} (hk : k ≤ blocks n) :
    LightSharedReportingLevels.roundTime (half n) (blocks n) k+8 ≤
      roundOverhead n*prefixBoxes n k := by
  have hV : (blocks n-k)*(512*half n) ≤ width n :=
    Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hdownset := (LightDownsetSize.time_bound ((blocks n-k)*(512*half n))).trans
    (Nat.mul_le_mul_left 1400 (Nat.pow_le_pow_left (Nat.add_le_add_right hV 1) 2))
  have hswitch := LightSwitchCosts.time_le_budget n k
  rw [← residual_eq] at hswitch
  have hcatalog := SharedReportingCosts.time_le_boxes hk
  have hextra : LightSwitch.time (SharedReportingBankLevels.residual (half n) (blocks n) k)+
      LightDownsetSize.time ((blocks n-k)*(512*half n))+2808 ≤ roundExtra n := by
    unfold roundExtra
    omega
  have hextraBoxes := Nat.le_mul_of_pos_right (roundExtra n) (prefixBoxes_pos n k)
  unfold LightSharedReportingLevels.roundTime LightSharedReportingCell.time LightSharedReportingEntry.time
  rw [cut_eq]
  change _ ≤ (SharedReportingCosts.overhead n+roundExtra n)*prefixBoxes n k
  change LightReportingCatalogIndex.time (half n) (blocks n) k
    (Switch.residualSize n k-Switch.actualSwitch n k) ≤
    SharedReportingCosts.overhead n*prefixBoxes n k at hcatalog
  rw [Nat.add_mul]
  omega

theorem all_prefix_pos (n : ℕ) : 0 < allPrefixBoxes n := by
  have h0 : 0 ∈ Finset.range (Switch.terminalDepth n+1) := by simp
  have hh := Finset.single_le_sum (f := fun k => prefixBoxes n k) (fun k _ => Nat.zero_le _) h0
  exact (prefixBoxes_pos n 0).trans_le hh

theorem pair_time_le (n : ℕ) :
    LightSharedReportingPair.time (half n) (blocks n) (SharedReportingBankHeader.levels (blocks n))+1000 ≤
      (roundOverhead n+1600)*allPrefixBoxes n := by
  have hsum : (∑ k ∈ Finset.range (Switch.terminalDepth n+1),
      (LightSharedReportingLevels.roundTime (half n) (blocks n) k+8)) ≤
      roundOverhead n*allPrefixBoxes n := by
    unfold allPrefixBoxes
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun k hk => round_time_le
      ((Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans (terminal_le_blocks n)))
  have hconstant := Nat.le_mul_of_pos_right 1600 (all_prefix_pos n)
  unfold LightSharedReportingPair.time LightSharedReportingLevels.time
  rw [levels_eq,Nat.add_mul]
  omega

theorem total_le {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    SharedReportingBankRows.total (half n) (blocks n) NB NC (BandScales.bandSize n) ≤
      3*bandCount n^2*TrimScales.scheduleCount n := by
  have hb := SourceBandCosts.size_le_bandCount hB
  have hc := SourceBandCosts.size_le_bandCount hC
  unfold SharedReportingBankRows.total SharedReportingBankRows.pairs
  rw [show LightBlockSourceCatalog.count (half n) (blocks n)=TrimScales.scheduleCount n from
    BlockSourceCatalogCosts.count_eq_scheduleCount n]
  calc
    _ ≤ TrimScales.scheduleCount n*bandCount n*bandCount n :=
      Nat.mul_le_mul (Nat.mul_le_mul_left _ hb) hc
    _ = bandCount n^2*TrimScales.scheduleCount n := by ring
    _ ≤ 3*bandCount n^2*TrimScales.scheduleCount n := by nlinarith

theorem host_time_le_sourceProof {NB NC n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    LightSharedReportingHost.time (half n) (blocks n) NB NC (BandScales.bandSize n) ≤ budget n := by
  have hproduct := Nat.mul_le_mul (total_le hB hC) (pair_time_le n)
  have hmain : SharedReportingBankRows.total (half n) (blocks n) NB NC (BandScales.bandSize n)*
      (LightSharedReportingPair.time (half n) (blocks n) (SharedReportingBankHeader.levels (blocks n))+1000) ≤
      (roundOverhead n+1600)*boxCount n := by
    convert hproduct using 1 <;> unfold boxCount <;> ring
  have hdepth := LightSwitchCosts.depth_time_le_budget n
  have hcounts := LightSharedReportingCounts.time_bound (half n)
  change LightSharedReportingCounts.time (half n) ≤ 1500*(localWidth n+1)^2 at hcounts
  change LightSwitchDepth.time (blocks n) ≤ LightSwitchCosts.depthBudget n at hdepth
  unfold LightSharedReportingHost.time LightSharedReportingBank.time
  unfold budget overhead setup
  nlinarith

noncomputable section

































end
end ThreeSum.SharedReportingBankCosts

end


theorem solution : ∀ {NB NC n : Nat},
  @LE.le.{0} Nat instLENat NB n →
    @LE.le.{0} Nat instLENat NC n →
      @LE.le.{0} Nat instLENat
        (ThreeSum.LightSharedReportingHost.time (ThreeSum.SharedReportingCosts.half n)
          (ThreeSum.SharedReportingCosts.blocks n) NB NC (ThreeSum.BandScales.bandSize n))
        (ThreeSum.SharedReportingBankCosts.budget n) := by
  exact @ThreeSum.SharedReportingBankCosts.host_time_le_sourceProof

#print axioms solution
