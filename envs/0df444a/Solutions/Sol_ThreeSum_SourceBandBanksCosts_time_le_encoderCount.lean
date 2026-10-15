-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.time_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T16:33:38.554113+00:00
-- url     : https://prove2.me/submissions/6e2151ee-ad2a-4581-9057-e62ffadd1274

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_work_le_encoderCount
import Theorems.Thm_ThreeSum_LocalCoverBounds_pow_le_choose_mul


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
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
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.Parameters
end ThreeSum.Parameters
namespace ThreeSum.Scales
end ThreeSum.Scales
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
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators




































theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < outputCount (512 * h) h := by
  have hlo : 256 ^ (2 * h) ≤ outputCount (512 * h) h := by
    simpa [outputCount, show 256 * (2 * h) = 512 * h by omega] using
      pow_le_choose_mul 256 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

























































































/-! ## A deterministic selected prime -/















































































/-! ## Exact integer rounding of the separable bucket cap -/































/-! ## The actual local parameters at `L=512*h` -/





























































end ThreeSum.LocalCoverBounds

end

section


/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000



































theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J




section OriginalSources

variable {β : Type*} [DecidableEq β]



























end OriginalSources

end ThreeSum.BlockSourceEncoding

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

theorem width_eq (n : ℕ) :
    blockCount (inputBits n)*(512*microHalf (inputBits n)) = 256*mu n := by
  unfold mu totalSize microSize microHalf
  ring

theorem cutoff_eq (n : ℕ) :
    2*microHalf (inputBits n)*blockCount (inputBits n) = mu n := by
  unfold mu totalSize microSize microHalf
  ring




























































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










theorem four_le_scheduleSize (h : ℕ) : 4 ≤ GlobalEncoding.scheduleSize h := by
  unfold GlobalEncoding.scheduleSize LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)

theorem localPrime_le_four_outputs (h : ℕ) : localPrime h ≤ 4*outputCount (512*h) h := by
  have ho : 2^(2*h) ≤ outputCount (512*h) h := by
    by_cases hz : h=0
    · simp [hz,outputCount]
    · exact (concrete_output_gt_pow (by omega)).le
  have hu := localPrime_sq_upper h
  have hm := Nat.mul_le_mul_left (16*outputCount (512*h) h) ho
  nlinarith

theorem modulus_le_global_outputs (h J : ℕ) :
    BlockSourceEncoding.modulus h J ≤ GlobalEncoding.scheduleSize h^J*
      (J*(512*h)).choose (J*(2*h)) := by
  have hl : localPrime h ≤ GlobalEncoding.scheduleSize h*outputCount (512*h) h :=
    (localPrime_le_four_outputs h).trans (Nat.mul_le_mul_right _ (four_le_scheduleSize h))
  have hp := Nat.pow_le_pow_left hl J
  rw [mul_pow] at hp
  unfold BlockSourceEncoding.modulus
  exact hp.trans (Nat.mul_le_mul_left _ (choose_pow_le (512*h) (2*h) J))

theorem modulus_le_tableCount (n : ℕ) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ tableCount n := by
  have hm := modulus_le_global_outputs (microHalf (inputBits n)) (blockCount (inputBits n))
  have hc : blockCount (inputBits n)*(2*microHalf (inputBits n))=mu n := by
    rw [Nat.mul_comm,BlockSourceSharing.cutoff_eq]
  rw [BlockSourceSharing.width_eq,hc] at hm
  change LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*fullOutputs n ≥ _ at hm
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount] at hm
  exact hm































theorem bands_modulus_le_encoderCount (n : ℕ) :
    bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*tableCount n := Nat.mul_le_mul_left _ (modulus_le_tableCount n)
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring

theorem bands_le_encoderCount (n : ℕ) : bandCount n ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) :=
      Nat.le_mul_of_pos_right _ (BlockSourceEncoding.modulus_pos _ _)
    _ ≤ _ := bands_modulus_le_encoderCount n

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


/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts

open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress














theorem count_le_bandCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandPairSlices.count NL NR (bandSize n) ≤ bandCount n :=
  max_le (SourceBandCosts.size_le_bandCount hNL) (SourceBandCosts.size_le_bandCount hNR)





















theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < bandCount n := by
  have hp := (bandCount_mul_bounds n).1
  by_contra h
  have hz : bandCount n=0 := by omega
  rw [hz,Nat.mul_zero] at hp
  omega

theorem time_le_encoderCount_sourceProof {NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandBanks.time NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+1300)*
        encoderCount n+1220 := by
  have hcount := count_le_bandCount hNL hNR
  have hpos := bandCount_pos hn
  have hrows := Nat.le_mul_of_pos_left
    (LightSourceOccurrenceArray.time
      (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
      (blockCount (inputBits n))) hpos
  have hbatch := Nat.mul_le_mul_right
    (LightBlockSourceBatch.time
      (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)) hcount
  have ht : LightSourceBandBanks.time NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      BlockSourceCatalogCosts.work n+1300*bandCount n+1220 := by
    unfold LightSourceBandBanks.time LightSourceBandBankBatch.time LightSourceBandBankStep.time
      BlockSourceCatalogCosts.work LightBlockSourceCatalog.time
    nlinarith
  have hw := BlockSourceCatalogCosts.work_le_encoderCount n
  have hb := SourceBandCosts.bands_le_encoderCount n
  nlinarith














































































end ThreeSum.SourceBandBanksCosts

end


theorem solution : ∀ {NL NR n : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) n →
    @LE.le.{0} Nat instLENat NL n →
      @LE.le.{0} Nat instLENat NR n →
        @LE.le.{0} Nat instLENat
          (ThreeSum.LightSourceBandBanks.time NL NR (ThreeSum.BandScales.bandSize n)
            (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
            (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)) (ThreeSum.Scales.mu n))
          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
            (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                  (ThreeSum.LightBlockSourceCatalogProgram.factor
                    (ThreeSum.Scales.microHalf (ThreeSum.Scales.inputBits n))
                    (ThreeSum.Scales.blockCount (ThreeSum.Scales.inputBits n)))
                  (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
                    (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                      (@OfNat.ofNat.{0} Nat (nat_lit 256) (instOfNatNat (nat_lit 256))) (ThreeSum.Scales.mu n))
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                (@OfNat.ofNat.{0} Nat (nat_lit 1300) (instOfNatNat (nat_lit 1300))))
              (ThreeSum.StageBounds.encoderCount n))
            (@OfNat.ofNat.{0} Nat (nat_lit 1220) (instOfNatNat (nat_lit 1220)))) := by
  exact @ThreeSum.SourceBandBanksCosts.time_le_encoderCount_sourceProof

#print axioms solution
