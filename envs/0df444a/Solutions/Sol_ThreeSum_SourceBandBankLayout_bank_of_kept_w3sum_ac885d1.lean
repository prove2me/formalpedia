-- Prove2me | solution 1 for ThreeSum.SourceBandBankLayout.bank_of_kept_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:32.117325+00:00
-- url     : https://prove2.me/submissions/a1a3fd99-1be6-4fa9-b418-7f23e510dad6

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalog
import Definitions.Def_Submission_ThreeSum_SourceBandPairSlices
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBankLayout
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_banks_le_work
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_left_cell_lt_next
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_masks_le_work
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_right_cell_lt_next
import Theorems.Thm_ThreeSum_LightBlockSourceBatchLayout_slot_le_masks


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBankLayout
open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder
namespace ThreeSum.SourceBandBankLayout
theorem _root_.solution {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i bound : ℕ} {μ ν : ℕ → ℤ} {p shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : GlobalOutput h J}
    (H : LightBlockSourceBatch.BankAt μ base count cut i p shift B b A a q)
    (hi : i < count) (K : Kept μ ν bound) (hb : work base count (J*(512*h)) cut ≤ bound) :
    LightBlockSourceBatch.BankAt ν base count cut i p shift B b A a q := by
  have hmask := masks_le_work base count (J*(512*h)) cut
  have hnext := slot_le_masks (base := base) (W := J*(512*h)) (cut := cut)
    (show i+1 ≤ count by omega)
  have hhead := banks_le_work base count (J*(512*h)) cut
  unfold banks at hhead
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj S hS
    have hs := left_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.left j hj S hS)
  · intro j hj S hS
    have hs := right_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.right j hj S hS)
  · exact (K _ (by omega)).trans H.headerLeft
  · exact (K _ (by omega)).trans H.headerRight
end ThreeSum.SourceBandBankLayout
