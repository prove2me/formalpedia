-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.wanted_selected_ends
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:23:26.364983+00:00
-- url     : https://prove2.me/submissions/78dbb2c2-ae77-4435-8a74-ca5d7898aaf0

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
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
import Theorems.Thm_ThreeSum_SharedReportingBankSources_source_bounds


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.BandPartition
end ThreeSum.BandPartition
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.ReportingHostSourceSelection
end ThreeSum.ReportingHostSourceSelection
namespace ThreeSum.ReportingHostSourceSelectionStored
end ThreeSum.ReportingHostSourceSelectionStored
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

section


/-!
# Consecutive bands of a strictly increasing array

The last band is truncated. Every input position belongs to its quotient
band, the bands are strictly separated, and each band has at most `g` entries.
The quotient in these specifications is realized by `LightBandPartition`.
-/

namespace ThreeSum.BandPartition




















































theorem length_le (n g i : ℕ) : stop n g i-start g i ≤ g := by
  have hle : stop n g i ≤ (i+1)*g := min_le_right _ _
  unfold start
  simp only [Nat.add_mul,Nat.one_mul] at hle
  omega


















































end ThreeSum.BandPartition

end

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega

theorem table_ends_le (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by
  unfold nextFree scheduleMaps candidates work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total LightCoverGreedy.out
  omega










































end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000







theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega






















































end ThreeSum.LightCoverKeyData

end

section


/-! # Packed original-band histograms and exact physical residue fibers -/

namespace ThreeSum.SourceBandLayout

open BandPartition LightHistogram SourceBuckets












theorem len_le_cap (n g i : ℕ) : len n g i ≤ cap n g := by
  have hn := stop_le n g i
  have hg := length_le n g i
  unfold len cap
  exact le_min (by omega) hg








theorem start_add_len {n g i : ℕ} (hg : 0 < g) (hi : i < size n g) :
    start g i+len n g i = stop n g i := by
  have hs := start_lt_stop hg hi
  unfold len
  omega











theorem hist_mono (base n g m : ℕ) : Monotone (hist base n g m) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem data_le_hist (base n g m i : ℕ) : data base n g ≤ hist base n g m i :=
  Nat.le_add_right _ _

theorem flat_end (base n g m i : ℕ) :
    flat base n g m i+cap n g = hist base n g m (i+1) := by
  unfold flat cursor offsets codes hist stride
  ring

theorem header_end {base n g m i : ℕ} (hi : i < size n g) :
    base+6*i+6 ≤ hist base n g m i := by
  have hb := data_le_hist base n g m i
  unfold data at hb
  omega

theorem flat_end_le_work {base n g m i : ℕ} (hi : i < size n g) :
    flat base n g m i+cap n g ≤ work base n g m := by
  rw [flat_end]
  exact hist_mono base n g m (by omega)




















































end ThreeSum.SourceBandLayout

end

section


/-! # Two retained original-band catalogs and one shared empty histogram -/

namespace ThreeSum.SourceBandPairData

open Light BandPartition






theorem work_ge (base n g m : ℕ) : base ≤ SourceBandLayout.work base n g m := by
  unfold SourceBandLayout.work SourceBandLayout.hist SourceBandLayout.data
  omega

theorem ordered (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩










































































end ThreeSum.SourceBandPairData

end

section


/-!
# Every selected persistent row remains before the counter

The bounds keep the selected B and C bands independent. Each incidence and
occurrence is selected by its retained physical label, and every translated
pointer is bounded individually by the already occupied prefix.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2800000
set_option maxRecDepth 15000

theorem wanted_band_row_ends {base n g m i : ℕ} (hi : i<BandPartition.size n g) :
    base+6*i+6≤SourceBandLayout.work base n g m ∧
    SourceBandLayout.offsets base n g m i+m+1≤SourceBandLayout.work base n g m ∧
    SourceBandLayout.flat base n g m i+SourceBandLayout.len n g i≤SourceBandLayout.work base n g m := by
  have hh := SourceBandLayout.header_end (base := base) (m := m) hi
  have hf := SourceBandLayout.flat_end_le_work (base := base) (m := m) hi
  have hl := SourceBandLayout.len_le_cap n g i
  refine ⟨?_,?_,(Nat.add_le_add_left hl _).trans hf⟩
  · unfold SourceBandLayout.flat SourceBandLayout.cursor SourceBandLayout.offsets SourceBandLayout.codes at hf
    omega
  · unfold SourceBandLayout.flat SourceBandLayout.cursor at hf
    omega

theorem wanted_cover_ends (cover h J : ℕ) :
    cover+20≤LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.scheduleMaps (LightLocalCoverInit.base cover) h+2*(512*h)*scheduleSize h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.candidates (LightLocalCoverInit.base cover) h+scheduleSize h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.hist0 (LightLocalCoverInit.base cover) h+LightLocalCoverSchedule.rows h*localPrime h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.hist1 (LightLocalCoverInit.base cover) h+LightLocalCoverSchedule.rows h*localPrime h≤
      LightCoverKeyData.keyEnd cover h J := by
  have hb := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base cover) h
  have ht := LightLocalCoverRetention.table_ends_le (LightLocalCoverInit.base cover) h
  have he := LightCoverKeyData.afterCover_le_keyEnd cover h J
  change LightLocalCoverMetadata.nextFree (LightLocalCoverInit.base cover) h≤_ at he
  refine ⟨hb.trans he,?_,ht.2.2.2.2.trans he,ht.2.1.trans he,ht.2.2.1.trans he⟩
  simpa only [LightLocalCoverMetadata.nextFree,Nat.mul_comm] using he























theorem wanted_selected_ends_sourceProof {pair bank cover srcB srcC NB NC g h J cut occ i j code stop : ℕ}
    (hg : 0<g) (hi : i<BandPartition.size NB g) (hj : j<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J)
    (hsrcB : srcB+NB≤stop) (hsrcC : srcC+NC≤stop)
    (hpair : SourceBandPairData.next pair NB NC g (modulus h J)≤stop)
    (hbank : SourceBandBankData.finish bank NB NC g h J cut≤stop)
    (hocc : occ+LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : LightCoverKeyData.keyEnd cover h J≤stop) :
    WantedSourceEnds (retained pair bank cover NB NC g h J cut occ i j code)
      pair bank cover srcB srcC i j code h J cut stop := by
  have hp := SourceBandPairData.ordered pair NB NC g (modulus h J)
  have hleftWork : SourceBandLayout.work (SourceBandPairData.leftBase pair) NB g (modulus h J)≤stop :=
    hp.2.1.trans (hp.2.2.le.trans hpair)
  have hrightWork : SourceBandLayout.work (SourceBandPairData.rightBase pair NB g (modulus h J)) NC g (modulus h J)≤stop := by
    exact hp.2.2.le.trans hpair
  have hleft := wanted_band_row_ends (base := SourceBandPairData.leftBase pair) (m := modulus h J) hi
  have hright := wanted_band_row_ends (base := SourceBandPairData.rightBase pair NB g (modulus h J))
    (m := modulus h J) hj
  have hstartL := SourceBandLayout.start_add_len hg hi
  have hstartR := SourceBandLayout.start_add_len hg hj
  have hstopL := BandPartition.stop_le NB g i
  have hstopR := BandPartition.stop_le NC g j
  have hbankBase : bank+5≤SourceBandBankData.finish bank NB NC g h J cut := by
    unfold SourceBandBankData.finish SourceBandBankData.first SourceBandBankLayout.baseAt
    omega
  have hsourceL := SharedReportingBankSources.source_bounds (base := bank) (NB := NB) (NC := NC) (h := h) (J := J) (cut := cut)
    (hi.trans_le (le_max_left _ _)) hk
  have hsourceR := SharedReportingBankSources.source_bounds (base := bank) (NB := NB) (NC := NC) (h := h) (J := J) (cut := cut)
    (hj.trans_le (le_max_right _ _)) hk
  have hcoverEnds := wanted_cover_ends cover h J
  have hmul := Nat.mul_le_mul_right J (show code+1≤LightBlockSourceCatalog.count h J from hk)
  simp only [Nat.add_mul,one_mul] at hmul
  refine ⟨?_,hbankBase.trans hbank,?_,hleft.1.trans hleftWork,hright.1.trans hrightWork,
    ?_,?_,?_,?_,hleft.2.1.trans hleftWork,hright.2.1.trans hrightWork,
    hleft.2.2.trans hleftWork,hright.2.2.trans hrightWork,?_,
    hcoverEnds.2.1.trans hcover,hcoverEnds.2.2.1.trans hcover,
    hcoverEnds.2.2.2.1.trans hcover,hcoverEnds.2.2.2.2.trans hcover,
    hsourceL.2.2.1.trans hbank,hsourceR.2.2.2.trans hbank⟩
  · unfold SourceBandPairData.leftBase at hp
    omega
  · omega
  · change SharedReportingBankSources.leftCell bank h J cut i code+1≤stop
    omega
  · change SharedReportingBankSources.rightCell bank h J cut j code+1≤stop
    omega
  · change srcB+BandPartition.start g i+SourceBandLayout.len NB g i≤stop
    omega
  · change srcC+BandPartition.start g j+SourceBandLayout.len NC g j≤stop
    omega
  · change occ+code*J+J≤stop
    omega









































end ThreeSum.SharedReportingBankResourceBounds

end


theorem solution : ∀ {pair bank cover srcB srcC NB NC g h J cut occ i j code stop : Nat},
  @LT.lt.{0} Nat instLTNat (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) g →
    @LT.lt.{0} Nat instLTNat i (ThreeSum.BandPartition.size NB g) →
      @LT.lt.{0} Nat instLTNat j (ThreeSum.BandPartition.size NC g) →
        @LT.lt.{0} Nat instLTNat code (ThreeSum.LightBlockSourceCatalog.count h J) →
          @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcB NB) stop →
            @LE.le.{0} Nat instLENat (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) srcC NC) stop →
              @LE.le.{0} Nat instLENat
                  (ThreeSum.SourceBandPairData.next pair NB NC g (ThreeSum.BlockSourceEncoding.modulus h J)) stop →
                @LE.le.{0} Nat instLENat (ThreeSum.SourceBandBankData.finish bank NB NC g h J cut) stop →
                  @LE.le.{0} Nat instLENat
                      (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) occ
                        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
                          (ThreeSum.LightBlockSourceCatalog.count h J) J))
                      bank →
                    @LE.le.{0} Nat instLENat (ThreeSum.LightCoverKeyData.keyEnd cover h J) stop →
                      ThreeSum.SharedReportingBankResourceBounds.WantedSourceEnds
                        (ThreeSum.ReportingHostSourceSelectionStored.retained pair bank cover NB NC g h J cut occ i j
                          code)
                        pair bank cover srcB srcC i j code h J cut stop := by
  exact @ThreeSum.SharedReportingBankResourceBounds.wanted_selected_ends_sourceProof

#print axioms solution
