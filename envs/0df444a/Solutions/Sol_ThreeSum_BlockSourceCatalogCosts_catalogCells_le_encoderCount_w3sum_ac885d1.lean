-- Prove2me | solution 1 for ThreeSum.BlockSourceCatalogCosts.catalogCells_le_encoderCount_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:22.634295+00:00
-- url     : https://prove2.me/submissions/8c4941cf-05d8-4158-ac50-6c2e9ed2c988

import Definitions.Def_Submission_ThreeSum_LightBlockSourceCatalogProgram
import Definitions.Def_Submission_ThreeSum_BlockSourceStageCosts
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_stride_add_two_le
import Theorems.Thm_ThreeSum_BlockSourceSharing_downset_add_one_le_fullOutputs


set_option autoImplicit false
open ThreeSum ThreeSum.BlockSourceCatalogCosts
open Scales TrimScales StageBounds CostLedger BlockSourceSharing SubsetAddress
open LightBlockSourceBatchLayout
namespace ThreeSum.BlockSourceCatalogCosts
theorem _root_.solution (n : ℕ) :
    catalogCells n ≤ (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*encoderCount n := by
  have hstride := stride_add_two_le (256*mu n) (mu n)
  have hJ : blockCount (inputBits n) ≤
      blockCount (inputBits n)*(downsetCap (256*mu n) (mu n)+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hslot : blockCount (inputBits n)+stride (256*mu n) (mu n)+2 ≤
      (blockCount (inputBits n)+2*(256*mu n)+7)*(downsetCap (256*mu n) (mu n)+1) := by
    nlinarith
  have hd := downset_add_one_le_fullOutputs n
  have he : bandCount n*scheduleCount n*fullOutputs n ≤ encoderCount n := by
    calc
      _ ≤ 2*(bandCount n*scheduleCount n*fullOutputs n) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ = encoderCount n := by unfold encoderCount; ring
  unfold catalogCells
  calc
    _ ≤ bandCount n*scheduleCount n*((blockCount (inputBits n)+2*(256*mu n)+7)*
        ((256*mu n+2)*fullOutputs n)) :=
      Nat.mul_le_mul_left _ (hslot.trans (Nat.mul_le_mul_left _ hd))
    _ = (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*
        (bandCount n*scheduleCount n*fullOutputs n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he
end ThreeSum.BlockSourceCatalogCosts
