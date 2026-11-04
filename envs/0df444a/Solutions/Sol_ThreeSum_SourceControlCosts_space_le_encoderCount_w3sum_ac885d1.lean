-- Prove2me | solution 1 for ThreeSum.SourceControlCosts.space_le_encoderCount_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:53:30.011499+00:00
-- url     : https://prove2.me/submissions/db3722c0-39a6-4b8e-891a-c61b1041b3da

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Theorems.Thm_ThreeSum_BlockSourceSharing_width_eq
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_space_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_input_le_encoderCount
import Definitions.Def_WeightedCache3SUM_Alias_efe4583c1ba8c927


set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceControlCosts
theorem _root_.solution {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n+
          (256*mu n+1)^2+(256*mu n+1))*encoderCount n+
        Nat.log 2 (scheduleCount n+1)+
        max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19 := by
  have hs := SourceBandHostCosts.space_le_encoderCount (base := base+3) (p := p) (U := U) (D := D) hn hNL hNR
  have he : 0 < encoderCount n := hn.trans_le (SourceBandCosts.input_le_encoderCount n)
  have hp := Nat.le_mul_of_pos_right ((256*mu n+1)^2+(256*mu n+1)) he
  have hlog : 0 ≤ Nat.log 2 (scheduleCount n+1) := Nat.zero_le _
  have hlogs : 0 ≤ max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2) := Nat.zero_le _
  unfold LightSourceControlsHost.space LightSourceControlsHost.sourceBase
  apply max_le
  · unfold LightSourceControls.space LightPascal.tableSize
    rw [BlockSourceSharing.width_eq]
    nlinarith
  · nlinarith
end ThreeSum.SourceControlCosts
