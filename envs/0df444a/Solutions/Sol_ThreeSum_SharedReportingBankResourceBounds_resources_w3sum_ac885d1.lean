-- Prove2me | solution 1 for ThreeSum.SharedReportingBankResourceBounds.resources_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T15:50:06.777369+00:00
-- url     : https://prove2.me/submissions/8a3d506f-5f99-4d15-81a0-e93354be2b9b

import Definitions.Def_Submission_ThreeSum_SharedReportingBankCosts
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_ThreeSum_SharedReportingBankResourceBounds
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_count_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_storage_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_local_pairs_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_space_le
import Theorems.Thm_ThreeSum_SharedReportingBankResourceBounds_index_word_mono
import Theorems.Thm_ThreeSum_BandPartition_size_le
import Theorems.Thm_ThreeSum_LightHistogram_count_le
import Theorems.Thm_ThreeSum_LightRadixKeys_word_mono
import Theorems.Thm_ThreeSum_LightSourceRowScan_count_le
import Theorems.Thm_ThreeSum_ModuloCounts_count_le
import Theorems.Thm_ThreeSum_ModuloRuntime_word_mono
import Theorems.Thm_ThreeSum_ReportingHostCatalogIndexCosts_sort_clog_le
import Theorems.Thm_ThreeSum_ReportingHostPackedCatalog_prefix_count_le_pow
import Theorems.Thm_ThreeSum_SharedReportingBankLevels_level_le
import Theorems.Thm_ThreeSum_SharedReportingBankRows_rowBase_mono
import Theorems.Thm_ThreeSum_SharedReportingBankRows_rowBase_next
import Theorems.Thm_ThreeSum_SourceBandBankLayout_word_mono


set_option autoImplicit false
open ThreeSum ThreeSum.SharedReportingBankResourceBounds
open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows
set_option maxHeartbeats 2800000
set_option maxRecDepth 14000
namespace ThreeSum.SharedReportingBankResourceBounds
theorem _root_.solution {lim : Limits} {free h J NB NC g n d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n)
    (hspace : free+extent h J n ≤ lim.space)
    (hword : (word h J n g : ℤ) ≤ lim.word)
    (hdepth : d+depth h J ≤ lim.depth) :
    LightSharedReportingHost.Resources lim free h J NB NC g d := by
  have budget (x : ℕ) (hx : x ≤ word h J n g) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hs := (space_le (free := free) (h := h) (J := J) (g := g) hB hC).trans hspace
  have hend : SharedReportingBankHeader.finish free h J NB NC g ≤ lim.space := (le_max_right _ _).trans hs
  have hNB := (BandPartition.size_le NB g).trans hB
  have hNC := (BandPartition.size_le NC g).trans hC
  have hmul := Nat.mul_le_mul_left (LightBlockSourceCatalog.count h J) hNB
  have hcount := count_le (h := h) (J := J) (k := levels J) le_rfl
  have hstorage := storage_le (h := h) (J := J) (k := levels J) le_rfl
  have hpowNonneg : (0 : ℤ) ≤ ((2^(512*h) : ℕ) : ℤ) := Int.natCast_nonneg _
  have hpairPowNonneg : (0 : ℤ) ≤ ((2^(2*(512*h)) : ℕ) : ℤ) := Int.natCast_nonneg _
  refine ⟨hs,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,?_,?_⟩
  · unfold LightSharedReportingBank.controlWord word control
    omega
  · unfold word; omega
  · unfold word; omega
  · have he := local_pairs_le h
    unfold word
    omega
  · unfold word; omega
  · unfold depth at hdepth
    omega
  · intro q hq
    refine ⟨budget _ ?_,?_,budget _ ?_,?_,budget _ ?_,?_,?_,?_,?_,?_,?_⟩
    · unfold word stateWord
      omega
    · rw [rowBase_next]
      exact (rowBase_mono _ h J (levels J) (show q+1 ≤ total h J NB NC g from hq)).trans hend
    · unfold word; omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      apply budget
      have hh := LightRadixKeys.word_mono (p := 2^(512*h)) (U := 2^(512*h)) hkJ
      unfold word
      omega
    · unfold word width localWidth
      omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      have hc := index_word_mono (W := width h J) (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      apply budget
      change LightReportingSortedCatalog.word (width h J) (LightReportingPrefixCatalog.count h k) ≤ _
      change LightReportingSortedCatalog.word (width h J) (LightReportingPrefixCatalog.count h k) ≤
        LightReportingSortedCatalog.word (width h J) (2^(2*width h J)) at hc
      unfold word
      omega
    · intro k hk
      have hv : (J-k)*(512*h) ≤ width h J := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
      have hm := Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul_right g hp) (Nat.mul_le_mul_right g hp))
      apply budget
      unfold word
      omega
    · intro k hk
      have hr : SharedReportingBankLevels.residual h J k ≤ 2*h*J := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have ht := Nat.pow_le_pow_left (show J+SharedReportingBankLevels.residual h J k+1001 ≤ J+2*h*J+1001 by omega) 64
      apply budget
      change (J+SharedReportingBankLevels.residual h J k+1001)^64 ≤ _
      unfold word
      omega
    · unfold depth at hdepth
      omega
    · unfold depth width localWidth at hdepth
      omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      have hc := ReportingHostCatalogIndexCosts.sort_clog_le (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      unfold depth width localWidth at hdepth
      omega
end ThreeSum.SharedReportingBankResourceBounds
