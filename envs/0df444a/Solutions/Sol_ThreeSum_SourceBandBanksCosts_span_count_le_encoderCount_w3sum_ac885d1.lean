-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.span_count_le_encoderCount_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:42:06.093887+00:00
-- url     : https://prove2.me/submissions/0b3c958f-3c40-4afa-8aa8-e2654bec56be

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_eq
import Definitions.Def_WeightedCache3SUM_Alias_c4f490770c837de5
import Theorems.Thm_ThreeSum_BlockSourceCatalogCosts_count_eq_scheduleCount
import Theorems.Thm_ThreeSum_BlockSourceSharing_downset_le_fullOutputs
import Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_outputs_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution {G n : ℕ} (hG : G ≤ bandCount n) :
    G*SourceBandBankLayout.span (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      storageFactor n*encoderCount n := by
  have hslot : G*scheduleCount n*(LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2) ≤
      (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*encoderCount n := by
    apply le_trans (b := BlockSourceCatalogCosts.catalogCells n)
    · calc
        _ ≤ bandCount n*scheduleCount n*(LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hG)
        _ ≤ bandCount n*scheduleCount n*(blockCount (inputBits n)+LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = _ := rfl
    · exact BlockSourceCatalogCosts.catalogCells_le_encoderCount n
  have hGF : G*fullOutputs n ≤ encoderCount n :=
    (Nat.mul_le_mul_right _ hG).trans (SourceBandCosts.bands_outputs_le_encoderCount n)
  have hGK : G*downsetCap (256*mu n) (mu n) ≤ (mu n+1)*encoderCount n := by
    calc
      _ ≤ G*((mu n+1)*fullOutputs n) := Nat.mul_le_mul_left _ (BlockSourceSharing.downset_le_fullOutputs n)
      _ = (mu n+1)*(G*fullOutputs n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hGF
  have hGE := hG.trans (SourceBandCosts.bands_le_encoderCount n)
  have hother := Nat.mul_le_mul_right
    (256*mu n+2+LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))) hGE
  calc
    _ = G*scheduleCount n*(LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2)+
        G*downsetCap (256*mu n) (mu n)+
        G*(256*mu n+2+LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))) := by
      rw [span_eq,BlockSourceCatalogCosts.count_eq_scheduleCount,BlockSourceSharing.width_eq]
      ring
    _ ≤ (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*encoderCount n+
        (mu n+1)*encoderCount n+
        encoderCount n*(256*mu n+2+LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))) :=
      Nat.add_le_add (Nat.add_le_add hslot hGK) hother
    _ = _ := by unfold storageFactor; ring
end ThreeSum.SourceBandBanksCosts
