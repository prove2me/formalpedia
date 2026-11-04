-- Prove2me | solution 1 for ThreeSum.LightBandPreprocessing.Procs.meets_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:03.536208+00:00
-- url     : https://prove2.me/submissions/f5713e82-44cf-4317-9087-d5da12b368fd

import Definitions.Def_Submission_ThreeSum_LightHeaderBands
import Definitions.Def_Submission_ThreeSum_LightBandPreprocessing
import Definitions.Def_WeightedCache3SUM_Alias_a6ca635f54b46105
import Theorems.Thm_Light_MatAt_keep
import Theorems.Thm_Light_Meets_mono_time
import Theorems.Thm_Light_Meets_of_body
import Theorems.Thm_Light_SegN_keep
import Theorems.Thm_Light_Seg_keep
import Theorems.Thm_Light_VecAt_keep
import Theorems.Thm_Light_getElem_powList
import Theorems.Thm_Light_length_powList
import Theorems.Thm_Light_sameFrame_cons_cons
import Theorems.Thm_Light_sameFrame_cons_nil
import Theorems.Thm_Light_sameFrame_nil
import Theorems.Thm_Light_sameFrame_nil_cons
import Theorems.Thm_Light_toNat_natCast_add_natCast
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_BandPartition_size_mono
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_coeff
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_minus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_negate
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_plus
import Theorems.Thm_ThreeSum_Karatsuba_asPolynomial_shift
import Theorems.Thm_ThreeSum_Karatsuba_length_minus
import Theorems.Thm_ThreeSum_Karatsuba_length_negate
import Theorems.Thm_ThreeSum_Karatsuba_length_plus
import Theorems.Thm_ThreeSum_Karatsuba_length_shift
import Theorems.Thm_ThreeSum_Karatsuba_minus_getD
import Theorems.Thm_ThreeSum_Karatsuba_plus_getD
import Theorems.Thm_ThreeSum_LightBandEnumeration_At_keep
import Definitions.Def_WeightedCache3SUM_Alias_4c62aff33317338c
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_time_mono
import Theorems.Thm_ThreeSum_LightBandEnumeration_width_mono
import Definitions.Def_WeightedCache3SUM_Alias_d9563e39a04084e5
import Definitions.Def_WeightedCache3SUM_Alias_fecb00c51dea7534
import Definitions.Def_WeightedCache3SUM_Alias_f2e191e7f7b92ebc
import Definitions.Def_WeightedCache3SUM_Alias_cd0e44d57dc54f82
import Definitions.Def_WeightedCache3SUM_Alias_35c8db9f38e66e96
import Definitions.Def_WeightedCache3SUM_Alias_54cf43efc96d8adf
import Theorems.Thm_ThreeSum_LightKaratsuba_window_sub
import Definitions.Def_WeightedCache3SUM_Alias_d98593d0ef804094
import Definitions.Def_WeightedCache3SUM_Alias_73246870e6a638ab
import Theorems.Thm_ThreeSum_LightSortedBands_Prepared_keep
import Definitions.Def_WeightedCache3SUM_Alias_695bd1ac490da0cc
import Definitions.Def_WeightedCache3SUM_Alias_f253b70ba796e513
import Theorems.Thm_ThreeSum_LightSortedBands_family_bounded
import Theorems.Thm_ThreeSum_SubsetAddress_isMask_zero
import Theorems.Thm_ThreeSum_SubsetAddress_layerOffset_zero
import Theorems.Thm_ThreeSum_SubsetAddress_natPositions_card
import Theorems.Thm_ThreeSum_SubsetAddress_weight_zero
attribute [local simp] Light.getElem_powList
attribute [local simp] Light.length_powList
attribute [local simp] Light.sameFrame_cons_cons
attribute [local simp] Light.sameFrame_cons_nil
attribute [local simp] Light.sameFrame_nil
attribute [local simp] Light.sameFrame_nil_cons
attribute [local simp] Light.toNat_natCast_add_natCast
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_coeff
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_minus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_negate
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_plus
attribute [local simp] ThreeSum.Karatsuba.asPolynomial_shift
attribute [local simp] ThreeSum.Karatsuba.length_minus
attribute [local simp] ThreeSum.Karatsuba.length_negate
attribute [local simp] ThreeSum.Karatsuba.length_plus
attribute [local simp] ThreeSum.Karatsuba.length_shift
attribute [local simp] ThreeSum.Karatsuba.minus_getD
attribute [local simp] ThreeSum.Karatsuba.plus_getD
attribute [local simp] ThreeSum.LightKaratsuba.window_sub
attribute [local simp] ThreeSum.SubsetAddress.isMask_zero
attribute [local simp] ThreeSum.SubsetAddress.layerOffset_zero
attribute [local simp] ThreeSum.SubsetAddress.natPositions_card
attribute [local simp] ThreeSum.SubsetAddress.weight_zero
set_option autoImplicit false
open ThreeSum ThreeSum.LightBandPreprocessing
open Light ThreeSum.BandPartition
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBandPreprocessing
namespace Procs
theorem _root_.solution {pMain srcA srcB srcC av ae bv be cv ce work g U d : ℕ} {μ : ℕ → ℤ}
    {originalA originalB originalC : List ℤ} (R : Procs P pMain) (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA + originalA.length ≤ srcB) (hsrcBC : srcB + originalB.length ≤ srcC)
    (hsrcCv : srcC + originalC.length ≤ av) (hav : av + originalA.length ≤ ae)
    (hae : ae + 2 + 2 * originalA.length ≤ bv) (hbv : bv + originalB.length ≤ be)
    (hbe : be + 2 + 2 * originalB.length ≤ cv) (hcv : cv + originalC.length ≤ ce)
    (hce : ce + 2 + 2 * originalC.length ≤ work)
    (hspace : space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d + depth originalA.length originalB.length originalC.length g ≤ lim.depth) (hAread : Seg μ srcA originalA)
    (hBread : Seg μ srcB originalB) (hCread : Seg μ srcC originalC) (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ))
    (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [srcA, originalA.length, srcB, originalB.length, srcC, originalC.length, g, av, ae, bv, be, cv, ce, work] μ
      (time originalA.length originalB.length originalC.length g)
      (fun r μ' => Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧ Kept μ μ' srcA) :=
  by
  have hspace' :
    work + (originalA.length + originalB.length + originalC.length) +
            LightBandEnumeration.count (size originalA.length g) (size originalB.length g) (size originalC.length g) +
          LightBandEnumeration.width (size originalA.length g) (size originalB.length g) (size originalC.length g) +
        1 ≤
      lim.space :=
    hspace
  have hnormSpaceA : LightSortedBands.space work originalA.length ≤ lim.space := by unfold LightSortedBands.space; omega
  have hnormSpaceB : LightSortedBands.space work originalB.length ≤ lim.space := by unfold LightSortedBands.space; omega
  have hnormSpaceC : LightSortedBands.space work originalC.length ≤ lim.space := by unfold LightSortedBands.space; omega
  have hnormWord (n : ℕ) (hn : n ≤ originalA.length + originalB.length + originalC.length) :
    ((n + g + 2 : ℕ) : ℤ) ≤ lim.word :=
    by
    have hh : n + g + 2 ≤ word originalA.length originalB.length originalC.length g U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hnormDepth (n : ℕ) (hn : n ≤ originalA.length + originalB.length + originalC.length) :
    (d + 1) + n + Nat.clog 2 n + 3 ≤ lim.depth :=
    by
    have hlog := Nat.clog_mono_right 2 hn
    unfold depth at hd
    omega
  have hgWord : ((g + 2 : ℕ) : ℤ) ≤ lim.word := by simpa using hnormWord 0 (by omega)
  have hdSmall : d + 4 ≤ lim.depth := by unfold depth at hd; omega
  apply Meets.of_body R.main
  unfold body time
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((R.prepare.meets (d := d + 1) (src := srcA) (values := av) (endpoints := ae) (work := work) hw hg (by omega)
              hav (by omega) hnormSpaceA (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hAread)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (R.prepare.meets (d := d + 1) (src := srcA) (values := av) (endpoints := ae) (work := work) hw hg (by omega)
            hav (by omega) hnormSpaceA (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hAread)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSortedBands.time, LightNormalize.time, sortTime, LightNormalize.dedupTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime] <;> omega)
    on_goal -1 =>
      (rintro aCount μ₁ ⟨haCount, hPreparedA, hkeep₁⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hBread₁ : Seg μ₁ srcB originalB := by
    intro i hi
    rw [hkeep₁ (srcB + i) (by omega) (by omega) (by omega) (by omega)]
    exact hBread i hi
  have hCread₁ : Seg μ₁ srcC originalC := by
    intro i hi
    rw [hkeep₁ (srcC + i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread i hi
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((R.prepare.meets (d := d + 1) (src := srcB) (values := bv) (endpoints := be) (work := work) hw hg (by omega)
              hbv (by omega) hnormSpaceB (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hBread₁)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (R.prepare.meets (d := d + 1) (src := srcB) (values := bv) (endpoints := be) (work := work) hw hg (by omega)
            hbv (by omega) hnormSpaceB (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hBread₁)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSortedBands.time, LightNormalize.time, sortTime, LightNormalize.dedupTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime] <;> omega)
    on_goal -1 =>
      (rintro bCount μ₂ ⟨hbCount, hPreparedB, hkeep₂⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hPreparedA₂ : LightSortedBands.Prepared μ₂ av ae g originalA :=
    by
    apply hPreparedA.transfer
    intro a ha
    apply hkeep₂ a <;> rcases ha with ha | ha <;> omega
  have hCread₂ : Seg μ₂ srcC originalC := by
    intro i hi
    rw [hkeep₂ (srcC + i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread₁ i hi
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          ((R.prepare.meets (d := d + 1) (src := srcC) (values := cv) (endpoints := ce) (work := work) hw hg (by omega)
              hcv hce hnormSpaceC (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hCread₂)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          (R.prepare.meets (d := d + 1) (src := srcC) (values := cv) (endpoints := ce) (work := work) hw hg (by omega)
            hcv hce hnormSpaceC (hnormWord _ (by omega)) (hnormDepth _ (by omega)) hCread₂)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSortedBands.time, LightNormalize.time, sortTime, LightNormalize.dedupTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime] <;> omega)
    on_goal -1 =>
      (rintro cCount μ₃ ⟨hcCount, hPreparedC, hkeep₃⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  have hPreparedA₃ : LightSortedBands.Prepared μ₃ av ae g originalA :=
    by
    apply hPreparedA₂.transfer
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  have hPreparedB₃ : LightSortedBands.Prepared μ₃ bv be g originalB :=
    by
    apply hPreparedB.transfer
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  obtain ⟨A, hsA, hASeg, hALen, hAMem, hAHeader, hACount, hAAt⟩ := hPreparedA₃.family hg
  obtain ⟨B, hsB, hBSeg, hBLen, hBMem, hBHeader, hBCount, hBAt⟩ := hPreparedB₃.family hg
  obtain ⟨C, hsC, hCSeg, hCLen, hCMem, hCHeader, hCCount, hCAt⟩ := hPreparedC.family hg
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  have hsa : aFamily.size ≤ size originalA.length g := size_mono hALen
  have hsb : bFamily.size ≤ size originalB.length g := size_mono hBLen
  have hsc : cFamily.size ≤ size originalC.length g := size_mono hCLen
  have hsan : aFamily.size ≤ originalA.length := hsa.trans (size_le _ _)
  have hsbn : bFamily.size ≤ originalB.length := hsb.trans (size_le _ _)
  have hscn : cFamily.size ≤ originalC.length := hsc.trans (size_le _ _)
  have hcountBound := LightBandEnumeration.count_mono hsa hsb hsc
  have hwidthBound := LightBandEnumeration.width_mono hsa hsb hsc
  have henumSpace : LightBandEnumeration.space work aFamily.size bFamily.size cFamily.size ≤ lim.space :=
    by
    unfold LightBandEnumeration.space
    omega
  have henumWord : (LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U : ℤ) ≤ lim.word :=
    by
    have hh :
      LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U ≤
        word originalA.length originalB.length originalC.length g U :=
      by
      unfold word LightBandEnumeration.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have henumDepth : (d + 1) + LightBandEnumeration.width aFamily.size bFamily.size cFamily.size + 5 ≤ lim.depth :=
    by
    unfold depth at hd
    omega
  have henumTime :
    LightHeaderBands.time aFamily.size bFamily.size cFamily.size ≤
      LightHeaderBands.time (size originalA.length g) (size originalB.length g) (size originalC.length g) :=
    Nat.add_le_add_right (LightBandEnumeration.time_mono hsa hsb hsc) 100
  have hrepA : Represents μ₃ av ae g hg originalA A hsA := ⟨hASeg, hALen, hAMem, hAHeader, hACount, hAAt⟩
  have hrepB : Represents μ₃ bv be g hg originalB B hsB := ⟨hBSeg, hBLen, hBMem, hBHeader, hBCount, hBAt⟩
  have hrepC : Represents μ₃ cv ce g hg originalC C hsC := ⟨hCSeg, hCLen, hCMem, hCHeader, hCCount, hCAt⟩
  focus
    ((first
        | refine _root_.Light.Ends.seqSelf ?_
        | refine _root_.Light.Ends.skipLast ?_);
      (repeat
          with_unfolding_none
            first
            | refine _root_.Light.Ends.seqAssoc ?_
            | refine _root_.Light.Ends.skipThen ?_))
    first
    |
      refine
        _root_.Light.Ends.callToThen
          (((R.enumerate.meets (d := d + 1) aFamily bFamily cFamily hw (by omega) (by omega) (by omega) henumSpace
                  henumWord henumDepth hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2
                  (LightSortedBands.family_bounded hg hsA hAMem hAU) (LightSortedBands.family_bounded hg hsB hBMem hBU)
                  (LightSortedBands.family_bounded hg hsC hCMem hCU)).mono_time
              henumTime)
            _ (by omega))
          ?_ ?_ ?_ ?_
    |
      refine
        _root_.Light.Ends.callToThen
          ((R.enumerate.meets (d := d + 1) aFamily bFamily cFamily hw (by omega) (by omega) (by omega) henumSpace
                henumWord henumDepth hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2
                (LightSortedBands.family_bounded hg hsA hAMem hAU) (LightSortedBands.family_bounded hg hsB hBMem hBU)
                (LightSortedBands.family_bounded hg hsC hCMem hCU)).mono_time
            henumTime)
          ?_ ?_ ?_ ?_
    on_goal -1 =>
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [LightSortedBands.time, LightNormalize.time, sortTime, LightNormalize.dedupTime] <;> first
            | omega
            | (ring_nf; omega))
    on_goal -1 => omega
    on_goal -1 =>
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, LightSortedBands.time, LightNormalize.time,
            sortTime, LightNormalize.dedupTime] <;> omega)
    on_goal -1 => (rintro result μ₄ ⟨hresult, htable, hkeep₄⟩; try with_unfolding_none refine _root_.Light.Ends.skip ?_)
  refine
    ⟨⟨A, hsA, B, hsB, C, hsC, hresult, hrepA.keep hkeep₄ (by omega) (by omega), hrepB.keep hkeep₄ (by omega) (by omega),
        hrepC.keep hkeep₄ (by omega) hce, htable⟩,
      ?_⟩
  intro a ha
  change μ₄ a = μ a
  rw [hkeep₄ a (by omega), hkeep₃ a (by omega) (by omega) (by omega) (by omega),
    hkeep₂ a (by omega) (by omega) (by omega) (by omega), hkeep₁ a (by omega) (by omega) (by omega) (by omega)]
end Procs
end ThreeSum.LightBandPreprocessing
