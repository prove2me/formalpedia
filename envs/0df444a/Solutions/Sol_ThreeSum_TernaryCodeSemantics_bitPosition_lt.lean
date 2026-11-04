-- Prove2me | solution 1 for ThreeSum.TernaryCodeSemantics.bitPosition_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:52:04.743066+00:00
-- url     : https://prove2.me/submissions/195cef3d-cc6e-477a-aa80-7e8ac5784c6a

import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_LightTernaryCodes
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Theorems.Thm_ThreeSum_SubsetAddress_IsMask_low


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryCodeSemantics
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryCodeSemantics
theorem _root_.solution {N : ℕ} (p : Fin N × Fin 2) : bitPosition p<2*N := by
  have hi := p.1.isLt
  have hb := p.2.isLt
  unfold bitPosition low
  omega
end ThreeSum.TernaryCodeSemantics
