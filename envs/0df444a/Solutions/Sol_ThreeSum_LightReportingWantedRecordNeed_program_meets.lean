-- Prove2me | solution 1 for ThreeSum.LightReportingWantedRecordNeed.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T18:37:34.34868+00:00
-- url     : https://prove2.me/submissions/3a415eeb-32f8-40a9-b49a-ab89af6e7438

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Theorems.Thm_ThreeSum_BandRawA_mem_row
import Theorems.Thm_ThreeSum_LightReportingWantedRecord_program_meets
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_WantedSourceEnds_values
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_query_scratch
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_query_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_buffers
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_decoder_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_depth_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_numeric_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_record_space_of_ok
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_scratch_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_terminal_word_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_wanted_work_le


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandCandidateRows
end ThreeSum.BandCandidateRows
namespace ThreeSum.BandEnumeration
end ThreeSum.BandEnumeration
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BandRawA
end ThreeSum.BandRawA
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockSourceOccurrenceOrder
end ThreeSum.BlockSourceOccurrenceOrder
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightReportingPrefixCatalog
end ThreeSum.LightReportingPrefixCatalog
namespace ThreeSum.LightReportingSuffixCatalog
end ThreeSum.LightReportingSuffixCatalog
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.RawReporting
end ThreeSum.RawReporting
namespace ThreeSum.ReportingHostFrontierLayout
end ThreeSum.ReportingHostFrontierLayout
namespace ThreeSum.ReportingHostLevelData
end ThreeSum.ReportingHostLevelData
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.ReportingHostWantedControls
end ThreeSum.ReportingHostWantedControls
namespace ThreeSum.ReportingHostWantedLayout
end ThreeSum.ReportingHostWantedLayout
namespace ThreeSum.ReportingHostWantedOriginal
end ThreeSum.ReportingHostWantedOriginal
namespace ThreeSum.ReportingHostWantedRecordData
end ThreeSum.ReportingHostWantedRecordData
namespace ThreeSum.Scales
end ThreeSum.Scales
namespace ThreeSum.SharedReportingBankData
end ThreeSum.SharedReportingBankData
namespace ThreeSum.SharedReportingBankHeader
end ThreeSum.SharedReportingBankHeader
namespace ThreeSum.SharedReportingBankLayout
end ThreeSum.SharedReportingBankLayout
namespace ThreeSum.SharedReportingBankLevels
end ThreeSum.SharedReportingBankLevels
namespace ThreeSum.SharedReportingBankResourceBounds
end ThreeSum.SharedReportingBankResourceBounds
namespace ThreeSum.SharedReportingBankRows
end ThreeSum.SharedReportingBankRows
namespace ThreeSum.SharedReportingBankSources
end ThreeSum.SharedReportingBankSources
namespace ThreeSum.StageBounds
end ThreeSum.StageBounds

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
# Exact A-value incidences of the physical band-owner catalog

Each successful owner contributes only its A band. Labels retain the
physical owner slot and the coordinate in the retained sorted A array.
Equal values and equal triples in different owner slots remain distinct.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000









































































































theorem mem_firstRows {n g i : ℕ} {rs : List Record} {l : Label} :
    l ∈ firstRows n g rs i ↔
      l.owner < i ∧ l ∈ row n g l.owner (rs.getD l.owner default) := by
  constructor
  · intro hl
    obtain ⟨owner,ho,hl⟩ := List.mem_flatMap.mp hl
    have he := (mem_row.mp hl).2.1
    subst owner
    exact ⟨List.mem_range.mp ho,hl⟩
  · rintro ⟨ho,hl⟩
    exact List.mem_flatMap.mpr ⟨l.owner,List.mem_range.mpr ho,hl⟩
















































end ThreeSum.BandRawA

end

section


/-!
# Physical incidence indices and their exact owner coordinates

An incidence at position `count owner + localA` retains that physical
owner and its sorted A coordinate. Every emitted index has exactly this
form, including equal values emitted by different owners.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows

set_option maxHeartbeats 1700000
set_option maxRecDepth 7000



































































theorem at_mem {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) : labelAt n g rs k ∈ items n g rs := by
  rw [labelAt,List.getD_eq_getElem _ _ hk]
  exact List.getElem_mem hk

theorem at_bounds {n g k : ℕ} {rs : List Record}
    (hk : k < (items n g rs).length) :
    (labelAt n g rs k).owner < rs.length ∧
      (ownerRecord n g rs k).flag=1 ∧
      BandPartition.start g (ownerRecord n g rs k).a ≤ (labelAt n g rs k).position ∧
      (labelAt n g rs k).position < BandPartition.stop n g (ownerRecord n g rs k).a := by
  have hh := mem_firstRows.mp (at_mem hk)
  have hr := mem_row.mp hh.2
  exact ⟨hh.1,hr.1,hr.2.2.1,hr.2.2.2⟩

























theorem values_getD {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by
  unfold values labelAt
  rw [List.getD_map_of_lt _ hk default 0]


























end ThreeSum.BandRawA

end

section


/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode

open OutputDecodeOrder OutputDecodeRecords GlobalEncoding

set_option maxHeartbeats 1500000





theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [code,pow_succ']
    omega




























theorem source_code_lt (h J k : ℕ) :
    code (scheduleSize h) (layerCount h) J k < scheduleSize h^J :=
  code_lt (schedule_pos h) (layerCount_pos h) J k











end ThreeSum.OutputDecodeOccurrenceCode

end

section


/-! # Exact occurrence/B-band/C-band row order and retained catalog ownership -/

namespace ThreeSum.SharedReportingBankRows

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankData SharedReportingBankLayout SharedReportingBankLevels
open LightReportingPrefixCatalog LightReportingSuffixCatalog ReportingHostLevelData

set_option maxHeartbeats 1800000






















theorem rank_lt {S nb nc s i j : ℕ} (hs : s < S) (hi : i < nb) (hj : j < nc) :
    rank nb nc s i j < pairs S nb nc := by
  have hx : s*nb+i < S*nb := calc
    _ < s*nb+nb := Nat.add_lt_add_left hi _
    _ = (s+1)*nb := by ring
    _ ≤ S*nb := Nat.mul_le_mul_right nb (by omega)
  calc
    _ < (s*nb+i)*nc+nc := Nat.add_lt_add_left hj _
    _ = (s*nb+i+1)*nc := by ring
    _ ≤ S*nb*nc := Nat.mul_le_mul_right nc (by omega)



















































































































end ThreeSum.SharedReportingBankRows

end

section


/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader

open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1900000















theorem payload_le_finish (free h J NB NC g : ℕ) :
    payload free h J NB NC g ≤ finish free h J NB NC g := Nat.le_add_right _ _












































































end ThreeSum.SharedReportingBankHeader

end

section


/-! # Constant-time row addresses and original-output reporting interfaces -/

namespace ThreeSum.SharedReportingBankAccess

open Light GlobalEncoding BlockIndexedQuery OutputDecodeRecords
open SharedReportingBankRows SharedReportingBankHeader SharedReportingBankLevels
open SharedReportingBankData SharedReportingBankSources

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000




























theorem record_end {free h J NB NC g s i j : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    recordAt free J NB NC g s i j+5*levels J ≤ payload free h J NB NC g := by
  have hr := rank_lt hs hi hj
  have hh := Nat.mul_le_mul_left (5*levels J) (show
    rank (BandPartition.size NB g) (BandPartition.size NC g) s i j+1 ≤ total h J NB NC g by exact hr)
  unfold recordAt slot rowRecord payload
  nlinarith









































































end ThreeSum.SharedReportingBankAccess

end

section


/-!
# A reusable finite scratch layout for every wanted slot

The capacity uses the original physical input counts and the retained
representation cap. Its memory bound does not charge any traversal time:
only the actual retained frontier cells are visited. A mask span of `2^W`
also bounds every partial-depth terminal candidate array.
-/

namespace ThreeSum.ReportingHostWantedLayout

open Finset GlobalEncoding RawIncidences RawReporting LocalCoverBounds
open ReportingHostFrontierLayout LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false



































































theorem make_bounds {root K W G T cap cap' : ℕ} (hc : cap≤cap') :
    Bounds (make root K W G T cap') root K W G T cap := by
  have hf : slot root cap (K+1)≤slot root cap' (K+1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  refine ⟨rfl,hf,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,?_,?_,le_rfl,le_rfl,le_rfl,?_,le_rfl,le_rfl⟩
  · simp only [make]
    omega
  · simp only [make]
    omega
  · rfl












section Mass

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]



































end Mass

end ThreeSum.ReportingHostWantedLayout

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


/-! # Polynomial relative resources for every physical wanted slot -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales StageBounds GlobalEncoding LocalCoverBounds
open SharedReportingBankLayout ReportingHostWantedLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 16000






theorem wanted_power_le (n e f : ℕ) (hef : e≤f) :
    (magnitude n)^e≤(magnitude n+1)^f :=
  (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (Nat.pow_le_pow_right (by omega) hef)



















































































theorem wanted_cells_le {n K N NB NC : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n) :
    wantedCells (half n) (blocks n) K N NB NC (wantedDecodeV n)≤wantedEnvelope n := by
  have hw := wanted_work_le hK hN hB hC
  have hn := wanted_numeric_le hK hN hB hC
  have hs := wanted_scratch_le n
  have h9 : (magnitude n+1)^9≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h7 : (magnitude n+1)^7≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h2 : (magnitude n+1)^2≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold wantedCells wantedEnvelope
  omega


















theorem wanted_words_le {n N : ℕ} (hN : N≤3*(magnitude n)^3) :
    LightReportingTerminal.word (half n) (blocks n)≤wantedEnvelope n ∧
    LightWantedDecode.word (wantedDecodeV n) N (half n) (blocks n)≤wantedEnvelope n ∧
    queryWord (half n) (blocks n) (BandScales.bandSize n)≤wantedEnvelope n := by
  have ht := wanted_terminal_word_le n
  have hd := wanted_decoder_word_le hN
  have hq := query_word_le n
  have h2 : (magnitude n+1)^2≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h4 : (magnitude n+1)^4≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h6 : (magnitude n+1)^6≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  unfold wantedEnvelope queryEnvelope at *
  omega










theorem wanted_envelope_positive (n : ℕ) : 2≤wantedEnvelope n := by
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope
  omega

noncomputable section













theorem wanted_buffers_of_ok {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    WantedBuffers lim dst (half n) (blocks n) K N NB NC (wantedDecodeV n) :=
  wanted_buffers ((Nat.add_le_add_left (wanted_cells_le hK hN hB hC) dst).trans hok.cells)

theorem wanted_envelope_word_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (wantedNeed n U).Ok lim dst d) : (wantedEnvelope n : ℤ)≤lim.word :=
  (Int.ofNat_le.mpr (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))).trans hok.word

theorem wanted_values_word_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (wantedNeed n U).Ok lim dst d) : ((2*U : ℕ) : ℤ)≤lim.word := by
  have he := wanted_envelope_positive n
  have hb : 2*U≤wantedEnvelope n*(U+1) :=
    (Nat.mul_le_mul_left 2 (Nat.le_succ _)).trans (Nat.mul_le_mul_right _ he)
  exact (Int.ofNat_le.mpr hb).trans hok.word












end
end ThreeSum.SharedReportingBankResourceBounds

end

section


/-!
# Concrete execution and query resources under the wanted reporter's Need

The actual two-procedure layout constructor runs once and stores the same
fourteen pointers. Every subsequent shared-catalog query uses those pointers
without constructing another catalog or clearing its reserved buffers.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 13000

theorem wanted_words_of_ok {lim : Limits} {dst n U N d : ℕ}
    (hN : N≤3*(magnitude n)^3) (hok : (wantedNeed n U).Ok lim dst d) :
    (LightReportingTerminal.word (half n) (blocks n) : ℤ)≤lim.word ∧
    (LightWantedDecode.word (wantedDecodeV n) N (half n) (blocks n) : ℤ)≤lim.word ∧
    (queryWord (half n) (blocks n) (BandScales.bandSize n) : ℤ)≤lim.word := by
  obtain ⟨ht,hd,hq⟩ := wanted_words_le hN
  have hw := wanted_envelope_word_of_ok hok
  exact ⟨(Int.ofNat_le.mpr ht).trans hw,(Int.ofNat_le.mpr hd).trans hw,(Int.ofNat_le.mpr hq).trans hw⟩







theorem wanted_count_word_of_ok {lim : Limits} {dst n U NB NC d : ℕ}
    (hB : NB≤n) (hC : NC≤n) (hok : (wantedNeed n U).Ok lim dst d) :
    ((NB*NC : ℕ) : ℤ)≤lim.word := by
  have hh := Nat.mul_le_mul (hB.trans (input_le_magnitude n)) (hC.trans (input_le_magnitude n))
  have hp := wanted_power_le n 2 10 (by decide)
  have he : NB*NC≤wantedEnvelope n := by
    simp only [pow_two] at hp
    unfold wantedEnvelope
    omega
  exact (Int.ofNat_le.mpr he).trans (wanted_envelope_word_of_ok hok)

theorem wanted_integer_word_of_ok {lim : Limits} {dst n U d : ℕ} {z : ℤ}
    (hz : |z|≤(U : ℤ)) (hok : (wantedNeed n U).Ok lim dst d) : |z|≤lim.word := by
  have hh := wanted_values_word_of_ok hok
  have hu : (0 : ℤ)≤(U : ℤ) := Int.natCast_nonneg _
  push_cast at hh
  omega

theorem wanted_sum_word_of_ok {lim : Limits} {dst n U d : ℕ} {a b : ℤ}
    (ha : |a|≤(U : ℤ)) (hb : |b|≤(U : ℤ))
    (hok : (wantedNeed n U).Ok lim dst d) : |a+b|≤lim.word := by
  have hh := wanted_values_word_of_ok hok
  have hs := abs_add_le a b
  push_cast at hh
  omega

theorem wanted_depth_of_ok {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    d+wantedDepth (half n) (blocks n) K N NB NC≤lim.depth :=
  (Nat.add_le_add_left (wanted_depth_le hK hN hB hC) d).trans hok.depth

theorem wanted_query_scratch_of_ok {lim : Limits} {dst n U K N NB NC report s i j k d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hk : k≤LightSwitchDepth.depth (blocks n))
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostLevelData.Scratch lim (half n) (blocks n) k
      (SharedReportingBankAccess.levelCatalog report (half n) (blocks n)
        NB NC (BandScales.bandSize n) s i j k)
      (BandRawA.finiteBandPositions NB (BandScales.bandSize n) i).card
      (BandRawA.finiteBandPositions NC (BandScales.bandSize n) j).card
      (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).maskBase
      (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).work := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have hl := make_bounds (root := ReportingHostWantedLayout.root dst (blocks n))
    (K := K) (W := LightBlockQuery.width (half n) (blocks n)) (G := groupSize (half n))
    (T := 2^(LightBlockQuery.width (half n) (blocks n)))
    (cap := capacityBound N NB NC (representationCap (half n) (blocks n)) (groupSize (half n))) le_rfl
  have hmasks : (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).maskBase+
      queryMaskSpan (half n) (blocks n)≤
      (LightReportingWantedLayout.layout dst (half n) (blocks n) K N NB NC).work := hl.queryMasks
  exact query_scratch hk hmasks H.query (wanted_words_of_ok hN hok).2.2




















end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # All twenty selected reporter values fit the actual word limit -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light BandRawA BandCandidateRows ReportingHostWantedControls
open ReportingHostSourceSelection

set_option maxHeartbeats 300000
set_option maxRecDepth 14000

theorem wanted_record_values_word {lim : Limits} {f : ℕ→ℤ}
    {n g idx pair bank cover NB NC h J cut occ code srcB srcC report stop : ℕ}
    {rs : List Record}
    (H : WantedSourceEnds
      (LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c
      code h J cut stop)
    (hstop : stop≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hav : |f (labelAt n g rs idx).position|≤lim.word)
    (ho : (labelAt n g rs idx).owner≤lim.space)
    (hb : (ownerRecord n g rs idx).b≤lim.space)
    (hc : (ownerRecord n g rs idx).c≤lim.space)
    (hcat : LightReportingWantedAccess.catalog n g rs idx report J NB NC code≤lim.space) :
    ∀ z∈ReportingHostWantedControls.record
      (ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report), |z|≤lim.word := by
  have hnat (v : ℕ) (hv : v≤lim.space) : |(v : ℤ)|≤lim.word := by
    simpa using (Int.ofNat_le.mpr hv).trans hw
  intro z hz
  simp only [ReportingHostWantedControls.record,ofAccess,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hav
  · exact hnat _ ho
  · exact hnat _ hb
  · exact hnat _ hc
  · exact hnat _ hcat
  all_goals
    apply hnat
    exact (H.values _ (by simp [ReportingHostSourceSelection.values])).trans hstop

theorem wanted_record_values_of_allocation {lim : Limits} {f : ℕ→ℤ}
    {n g records idx pair bank cover NB NC h J cut occ code srcB srcC report stop : ℕ}
    {rs : List Record}
    (H : WantedSourceEnds
      (LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c
      code h J cut stop)
    (hidx : idx<(items n g rs).length)
    (hi : (ownerRecord n g rs idx).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs idx).c<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J)
    (hrecords : records+4*rs.length≤stop) (hsrcB : srcB+NB≤stop) (hsrcC : srcC+NC≤stop)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤stop)
    (hstop : stop≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hav : |f (labelAt n g rs idx).position|≤lim.word) :
    ∀ z∈ReportingHostWantedControls.record
      (ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report), |z|≤lim.word := by
  have ho := (at_bounds hidx).1
  have hb := hi.trans_le (BandPartition.size_le NB g)
  have hc := hj.trans_le (BandPartition.size_le NC g)
  have he := SharedReportingBankAccess.record_end (free := report) (J := J) hk hi hj
  have hf := SharedReportingBankHeader.payload_le_finish report h J NB NC g
  apply wanted_record_values_word H hstop hw hav (by omega) (by omega) (by omega)
  unfold LightReportingWantedAccess.catalog
  omega

end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # Word bounds for every physical scan prefix, including later prefixes -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light

theorem wanted_guard_word_of_mass_bound {lim : Limits} {dst n U old mass threshold d : ℕ}
    (hold : old≤3*(magnitude n)^7) (hmass : mass≤3*(magnitude n)^7)
    (hthreshold : threshold≤9*(magnitude n)^8)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ((old+mass+threshold+2 : ℕ) : ℤ)≤lim.word := by
  have h7 := wanted_power_le n 7 10 (by decide)
  have h8 := wanted_power_le n 8 10 (by decide)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  have hh : old+mass+threshold+2≤wantedEnvelope n := by
    unfold wantedEnvelope
    omega
  exact (Int.ofNat_le.mpr hh).trans (wanted_envelope_word_of_ok hok)

end ThreeSum.SharedReportingBankResourceBounds

end

section


/-! # The concrete wanted Need runs the original-owner record call -/

namespace ThreeSum.LightReportingWantedRecordNeed

open Light Finset BandRawA BandCandidateRows GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting BlockEncoding BlockForced BlockMaskLayout BlockCoefficientRows
open ReportingHostWantedOriginal ReportingHostWantedControls ReportingHostWantedLayout
open ReportingHostFrontierLayout ReportingHostSourceSelectionStored OutputDecodeRecords
open ReportingHostWantedRecordData SharedReportingBankResourceBounds

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
set_option linter.unusedSectionVars false

theorem program_meets_sourceProof {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n U NA NB NC pair bank cover p occ srcB srcC records report output dst counter K old threshold d i : ℕ}
    {rs : List Record} {shift : ℤ}
    (w : Wanted (half n) (blocks n) (AType NA (BandScales.bandSize n) rs))
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC (BandScales.bandSize n) p
      (BlockSourceEncoding.modulus (half n) (blocks n)) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC (BandScales.bandSize n) (half n) (blocks n)
      (LightBlockQuery.sourceCut (half n) (blocks n)) occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover (half n) (blocks n))
    (HQ : SharedReportingBankHeader.Stored μ report (half n) (blocks n) NB NC
      (BandScales.bandSize n) fB fC (p : ℤ) shift)
    (hi : (ownerRecord NA (BandScales.bandSize n) rs w.1.val).b<BandPartition.size NB (BandScales.bandSize n))
    (hj : (ownerRecord NA (BandScales.bandSize n) rs w.1.val).c<BandPartition.size NC (BandScales.bandSize n))
    (houtput : output<localCount (half n)^blocks n)
    (he : w.2.2=LightOutputDecodeOriginal.output (half n) (blocks n) output)
    (hp : 0<p) (hguard : 4*(p : ℤ)≤globalModulus (half n) (blocks n))
    (hK : K≤LightSwitchDepth.depth (blocks n)) (hKJ : K≤blocks n)
    (hkey : globalModulus (half n) (blocks n)∣valueAt NA (BandScales.bandSize n) rs fA w.1.val%(p : ℤ)+
      lift w.2.1*(p : ℤ)+shift-globalKey w.2.2)
    (hselected : Seg μ (access dst (blocks n))
      (record (selected fA NA NB NC (BandScales.bandSize n) pair bank cover (half n) (blocks n)
        occ srcB srcC report rs w output)))
    (hlayout : SegN μ dst (values (LightReportingWantedLayout.layout dst (half n) (blocks n) K
      (items NA (BandScales.bandSize n) rs).length NB NC)))
    (hdecoded : LightWantedDecode.Stored μ (decoded dst)
      (items NA (BandScales.bandSize n) rs).length (half n) (blocks n) i output)
    (hcounter : counter+4≤dst)
    (hcounterRead : μ counter=(old : ℤ)) (hthresholdRead : μ (counter+1)=(threshold : ℤ))
    (hends : WantedSourceEnds
      (LightReportingWantedAccess.selection NA (BandScales.bandSize n) rs w.1.val pair bank cover NB NC
        (half n) (blocks n) (LightBlockQuery.sourceCut (half n) (blocks n)) occ
        (OutputDecodeOccurrenceCode.code (scheduleSize (half n)) (layerCount (half n)) (blocks n) output))
      pair bank cover srcB srcC (ownerRecord NA (BandScales.bandSize n) rs w.1.val).b
      (ownerRecord NA (BandScales.bandSize n) rs w.1.val).c
      (OutputDecodeOccurrenceCode.code (scheduleSize (half n)) (layerCount (half n)) (blocks n) output)
      (half n) (blocks n) (LightBlockQuery.sourceCut (half n) (blocks n)) counter)
    (hrecords : records+4*rs.length≤counter) (hsrcB : srcB+NB≤counter) (hsrcC : srcC+NC≤counter)
    (hbank : SourceBandBankData.finish bank NB NC (BandScales.bandSize n) (half n) (blocks n)
      (LightBlockQuery.sourceCut (half n) (blocks n))≤report)
    (hreport : SharedReportingBankHeader.finish report (half n) (blocks n) NB NC (BandScales.bandSize n)≤counter)
    (hN : (items NA (BandScales.bandSize n) rs).length≤3*(magnitude n)^3)
    (hB : NB≤n) (hC : NC≤n)
    (hold : old≤3*(magnitude n)^7)
    (hmass : rootMass (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w≤3*(magnitude n)^7)
    (hthreshold : threshold≤9*(magnitude n)^8)
    (hreadB : ∀ j<NB, μ (srcB+j)=fB j) (hreadC : ∀ j<NC, μ (srcC+j)=fC j)
    (hvaluesB : ∀ j<NB, |fB j|≤(U : ℤ)) (hvaluesC : ∀ j<NC, |fC j|≤(U : ℤ))
    (hvalue : |fA (BandRawA.labelAt NA (BandScales.bandSize n) rs w.1.val).position|≤(U : ℤ))
    (hok : (wantedNeed n U).Ok lim dst d) :
    let S := selected fA NA NB NC (BandScales.bandSize n) pair bank cover (half n) (blocks n)
      occ srcB srcC report rs w output
    let D := catalogs NA NB NC (BandScales.bandSize n) report (half n) (blocks n) rs w output
    Meets lim LightReportingWantedRecordCall.program 138 d
      [access dst (blocks n),dst,half n,blocks n,K,BlockSourceEncoding.modulus (half n) (blocks n),cover,counter] μ
      (LightReportingWanted.time p shift (left rs fB w) (right rs fC w) S.NL S.NR old threshold
        (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w D K+4000)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+rootMass
          (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w ∨
          Terminal (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w K) ∧
        ν counter=((old+rootMass
          (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w : ℕ) : ℤ) ∧
        KeptBut μ ν (packed dst (blocks n)) counter 1) := by
  have hs : counter≤lim.space := by have hh := hok.cells; omega
  have hc : cover+8≤dst := by have hh := hends.coverHeader; omega
  have hav := wanted_integer_word_of_ok hvalue hok
  have hva : |valueAt NA (BandScales.bandSize n) rs fA w.1.val|≤(U : ℤ) := by
    simpa only [valueAt,values_getD fA w.1.isLt] using hvalue
  have hw := wanted_record_values_of_allocation hends w.1.isLt hi hj
    (OutputDecodeOccurrenceCode.source_code_lt (half n) (blocks n) output)
    hrecords hsrcB hsrcC hreport hs hok.space hav
  exact LightReportingWantedRecord.program_meets w HP HB HC HQ hi hj houtput he
    (BandScales.bandSize_pos n) hp hguard hK hKJ hkey hselected hlayout hdecoded
    hcounter hcounterRead hthresholdRead hends hbank hreport
    (wanted_buffers_of_ok hKJ hN hB hC hok)
    (fun k hk => wanted_query_scratch_of_ok hKJ hN hB hC (hk.trans hK) hok)
    hok.space (wanted_record_space_of_ok hKJ hN hB hC hc (by omega) hok) hw
    (wanted_guard_word_of_mass_bound hold hmass hthreshold hok) (wanted_words_of_ok hN hok).1
    hreadB hreadC (fun j hj' => wanted_integer_word_of_ok (hvaluesB j hj') hok)
    (fun j hj' => wanted_integer_word_of_ok (hvaluesC j hj') hok)
    (fun j hj' => wanted_sum_word_of_ok hva (hvaluesB j hj') hok)
    (wanted_count_word_of_ok hB hC hok) (wanted_depth_of_ok hKJ hN hB hC hok)

end ThreeSum.LightReportingWantedRecordNeed

end


theorem solution : ∀ {lim : Light.Limits} {μ fA fB fC : Nat → Int}
  {n U NA NB NC pair bank cover p occ srcB srcC records report output dst counter K old threshold d i : Nat}
  {rs : List.{0} ThreeSum.BandCandidateRows.Record} {shift : Int}
  (w :
    ThreeSum.RawReporting.Wanted.{0} (ThreeSum.SharedReportingBankResourceBounds.half n)
      (ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs))
  (HP :
    ThreeSum.SourceBandPairData.Stored μ fB fC pair NB NC (ThreeSum.BandScales.bandSize n) p
      (ThreeSum.BlockSourceEncoding.modulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      shift)
  (HB :
    ThreeSum.SourceBandBankData.Stored μ fB fC bank NB NC (ThreeSum.BandScales.bandSize n)
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      occ (@Nat.cast.{0} Int instNatCastInt p) shift)
  (HC :
    ThreeSum.LightCoverKeyData.Stored μ cover (ThreeSum.SharedReportingBankResourceBounds.half n)
      (ThreeSum.SharedReportingBankResourceBounds.blocks n))
  (HQ :
    ThreeSum.SharedReportingBankHeader.Stored μ report (ThreeSum.SharedReportingBankResourceBounds.half n)
      (ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC (ThreeSum.BandScales.bandSize n) fB fC
      (@Nat.cast.{0} Int instNatCastInt p) shift)
  (hi :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).b
      (ThreeSum.BandPartition.size NB (ThreeSum.BandScales.bandSize n)))
  (hj :
    @LT.lt.{0} Nat instLTNat
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).c
      (ThreeSum.BandPartition.size NC (ThreeSum.BandScales.bandSize n)))
  (houtput :
    @LT.lt.{0} Nat instLTNat output
      (@HPow.hPow.{0, 0, 0} Nat Nat Nat
        (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
        (ThreeSum.OutputDecodeRecords.localCount (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (he :
    @Eq.{1}
      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n))
        (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
          (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
          w))
      (ThreeSum.LightOutputDecodeOriginal.output (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n) output))
  (hp : @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) p)
  (hguard :
    @LE.le.{0} Int Int.instLEInt
      (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
        (@OfNat.ofNat.{0} Int (nat_lit 4) (@instOfNat (nat_lit 4))) (@Nat.cast.{0} Int instNatCastInt p))
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hK :
    @LE.le.{0} Nat instLENat K (ThreeSum.LightSwitchDepth.depth (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
  (hKJ : @LE.le.{0} Nat instLENat K (ThreeSum.SharedReportingBankResourceBounds.blocks n))
  (hkey :
    @Dvd.dvd.{0} Int Int.instDvd
      (ThreeSum.GlobalEncoding.globalModulus (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (@HSub.hSub.{0, 0, 0} Int Int Int (@instHSub.{0} Int Int.instSub)
        (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
          (@HAdd.hAdd.{0, 0, 0} Int Int Int (@instHAdd.{0} Int Int.instAdd)
            (@HMod.hMod.{0, 0, 0} Int Int Int (@instHMod.{0} Int Int.instMod)
              (ThreeSum.BandRawA.valueAt NA (ThreeSum.BandScales.bandSize n) rs fA
                (@Fin.val
                  (@List.length.{0} ThreeSum.BandRawA.Label
                    (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
                  (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p))
            (@HMul.hMul.{0, 0, 0} Int Int Int (@instHMul.{0} Int Int.instMul)
              (ThreeSum.RawIncidences.lift
                (@Prod.fst.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                  (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n))
                  (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
                    (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                      (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                        (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                    w)))
              (@Nat.cast.{0} Int instNatCastInt p)))
          shift)
        (@ThreeSum.GlobalEncoding.globalKey (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n)
          (@Prod.snd.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
            (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            (@Prod.snd.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w)))))
  (hselected :
    Light.Seg μ (ThreeSum.ReportingHostWantedLayout.access dst (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      (ThreeSum.ReportingHostWantedControls.record
        (ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (ThreeSum.BandScales.bandSize n) pair bank cover
          (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) occ
          srcB srcC report rs w output)))
  (hlayout :
    Light.SegN μ dst
      (ThreeSum.ReportingHostWantedLayout.values
        (ThreeSum.LightReportingWantedLayout.layout dst (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) K
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)) NB
          NC)))
  (hdecoded :
    ThreeSum.LightWantedDecode.Stored μ (ThreeSum.ReportingHostWantedLayout.decoded dst)
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) i
      output)
  (hcounter :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
        (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4))))
      dst)
  (hcounterRead : @Eq.{1} Int (μ counter) (@Nat.cast.{0} Int instNatCastInt old))
  (hthresholdRead :
    @Eq.{1} Int
      (μ
        (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) counter
          (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
      (@Nat.cast.{0} Int instNatCastInt threshold))
  (hends :
    ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
      (ThreeSum.LightReportingWantedAccess.selection NA (ThreeSum.BandScales.bandSize n) rs
        (@Fin.val
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
          (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
            (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
              (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
            w))
        pair bank cover NB NC (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n))
        occ
        (ThreeSum.OutputDecodeOccurrenceCode.code
          (ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.SharedReportingBankResourceBounds.half n))
          (ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.SharedReportingBankResourceBounds.half n))
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) output))
      pair bank cover srcB srcC
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).b
      (ThreeSum.BandRawA.ownerRecord NA (ThreeSum.BandScales.bandSize n) rs
          (@Fin.val
            (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
            (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
              (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
              w))).c
      (ThreeSum.OutputDecodeOccurrenceCode.code
        (ThreeSum.GlobalEncoding.scheduleSize (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.OutputDecodeRecords.layerCount (ThreeSum.SharedReportingBankResourceBounds.half n))
        (ThreeSum.SharedReportingBankResourceBounds.blocks n) output)
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
      (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n))
      counter)
  (hrecords :
    @LE.le.{0} Nat instLENat
      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) records
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 4) (instOfNatNat (nat_lit 4)))
          (@List.length.{0} ThreeSum.BandCandidateRows.Record rs)))
      counter)
  (hsrcB : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB NB) counter)
  (hsrcC : @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC NC) counter)
  (hbank :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SourceBandBankData.finish bank NB NC (ThreeSum.BandScales.bandSize n)
        (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (ThreeSum.LightBlockQuery.sourceCut (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
      report)
  (hreport :
    @LE.le.{0} Nat instLENat
      (ThreeSum.SharedReportingBankHeader.finish report (ThreeSum.SharedReportingBankResourceBounds.half n)
        (ThreeSum.SharedReportingBankResourceBounds.blocks n) NB NC (ThreeSum.BandScales.bandSize n))
      counter)
  (hN :
    @LE.le.{0} Nat instLENat
      (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))))
  (hB : @LE.le.{0} Nat instLENat NB n) (hC : @LE.le.{0} Nat instLENat NC n)
  (hold :
    @LE.le.{0} Nat instLENat old
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
  (hmass :
    @LE.le.{0} Nat instLENat
      (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
        (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
        (instDecidableEqFin
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
        (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n)
        (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs fA fB fC
          shift w)
        w)
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7))))))
  (hthreshold :
    @LE.le.{0} Nat instLENat threshold
      (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
        (@OfNat.ofNat.{0} Nat (nat_lit 9) (instOfNatNat (nat_lit 9)))
        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
          (@instHPow.{0, 0} Nat Nat (@NPow.toPow.{0} Nat (@Monoid.toNPow.{0} Nat Nat.instMonoid)))
          (ThreeSum.SharedReportingBankResourceBounds.magnitude n)
          (@OfNat.ofNat.{0} Nat (nat_lit 8) (instOfNatNat (nat_lit 8))))))
  (hreadB :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB j)) (fB j))
  (hreadC :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NC →
        @Eq.{1} Int (μ (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC j)) (fC j))
  (hvaluesB :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NB →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fB j))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hvaluesC :
    ∀ (j : Nat),
      @LT.lt.{0} Nat instLTNat j NC →
        @LE.le.{0} Int Int.instLEInt (@abs.{0} Int instLatticeInt Int.instAddGroup (fC j))
          (@Nat.cast.{0} Int instNatCastInt U))
  (hvalue :
    @LE.le.{0} Int Int.instLEInt
      (@abs.{0} Int instLatticeInt Int.instAddGroup
        (fA
          (ThreeSum.BandRawA.labelAt NA (ThreeSum.BandScales.bandSize n) rs
              (@Fin.val
                (@List.length.{0} ThreeSum.BandRawA.Label
                  (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs))
                (@Prod.fst.{0, 0} (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs)
                  (Prod.{0, 0} (Fin (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
                    (ThreeSum.GlobalEncoding.GlobalOutput (ThreeSum.SharedReportingBankResourceBounds.half n)
                      (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                  w))).position))
      (@Nat.cast.{0} Int instNatCastInt U))
  (hok : (ThreeSum.SharedReportingBankResourceBounds.wantedNeed n U).Ok lim dst d),
  have S :=
    ThreeSum.ReportingHostWantedRecordData.selected fA NA NB NC (ThreeSum.BandScales.bandSize n) pair bank cover
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) occ srcB
      srcC report rs w output;
  have D :=
    ThreeSum.ReportingHostWantedRecordData.catalogs NA NB NC (ThreeSum.BandScales.bandSize n) report
      (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) rs w
      output;
  Light.Meets lim ThreeSum.LightReportingWantedRecordCall.program
    (@OfNat.ofNat.{0} Nat (nat_lit 138) (instOfNatNat (nat_lit 138))) d
    (@List.cons.{0} Int
      (@Nat.cast.{0} Int instNatCastInt
        (ThreeSum.ReportingHostWantedLayout.access dst (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
      (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt dst)
        (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankResourceBounds.half n))
          (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt K)
              (@List.cons.{0} Int
                (@Nat.cast.{0} Int instNatCastInt
                  (ThreeSum.BlockSourceEncoding.modulus (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n)))
                (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt cover)
                  (@List.cons.{0} Int (@Nat.cast.{0} Int instNatCastInt counter) (@List.nil.{0} Int)))))))))
    μ
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat)
      (@ThreeSum.LightReportingWanted.time.{0, 0, 0}
        (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
        (instDecidableEqFin
          (@List.length.{0} ThreeSum.BandRawA.Label (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
        (ThreeSum.SharedReportingBankResourceBounds.half n) (ThreeSum.SharedReportingBankResourceBounds.blocks n) p
        shift
        (@ThreeSum.ReportingHostWantedOriginal.left (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA (ThreeSum.BandScales.bandSize n) rs fB w)
        (@ThreeSum.ReportingHostWantedOriginal.right (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA (ThreeSum.BandScales.bandSize n) rs fC w)
        S.NL S.NR old threshold
        (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
          (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs fA fB fC
          shift w)
        w D K)
      (@OfNat.ofNat.{0} Nat (nat_lit 4000) (instOfNatNat (nat_lit 4000))))
    fun (r : Int) (ν : Nat → Int) =>
    And
      (Or (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 0) (@instOfNat (nat_lit 0))))
        (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1)))))
      (And
        (Iff (@Eq.{1} Int r (@OfNat.ofNat.{0} Int (nat_lit 1) (@instOfNat (nat_lit 1))))
          (Or
            (@LT.lt.{0} Nat instLTNat threshold
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                  (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
                  (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)
                  (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs
                    fA fB fC shift w)
                  w)))
            (ThreeSum.ReportingHostWantedOriginal.Terminal (ThreeSum.SharedReportingBankResourceBounds.half n)
              (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs fA fB
              fC shift w K)))
        (And
          (@Eq.{1} Int (ν counter)
            (@Nat.cast.{0} Int instNatCastInt
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) old
                (@ThreeSum.ReportingHostFrontierLayout.rootMass.{0, 0, 0}
                  (ThreeSum.ReportingHostWantedOriginal.AType NA (ThreeSum.BandScales.bandSize n) rs) (Fin NB) (Fin NC)
                  (instDecidableEqFin
                    (@List.length.{0} ThreeSum.BandRawA.Label
                      (ThreeSum.BandRawA.items NA (ThreeSum.BandScales.bandSize n) rs)))
                  (ThreeSum.SharedReportingBankResourceBounds.half n)
                  (ThreeSum.SharedReportingBankResourceBounds.blocks n)
                  (ThreeSum.ReportingHostWantedOriginal.localItems (ThreeSum.SharedReportingBankResourceBounds.half n)
                    (ThreeSum.SharedReportingBankResourceBounds.blocks n) NA NB NC (ThreeSum.BandScales.bandSize n) p rs
                    fA fB fC shift w)
                  w))))
          (Light.KeptBut μ ν
            (ThreeSum.ReportingHostWantedLayout.packed dst (ThreeSum.SharedReportingBankResourceBounds.blocks n))
            counter (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) := by
  exact @ThreeSum.LightReportingWantedRecordNeed.program_meets_sourceProof

#print axioms solution
