-- Prove2me | solution 1 for ThreeSum.MaskDecode.decode_card_layer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:36.858545+00:00
-- url     : https://prove2.me/submissions/0612e234-79e8-4bff-a64b-317449aa488d

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_ThreeSum_MaskDecode_decode_card
import Theorems.Thm_ThreeSum_SubsetAddress_mem_enumerateLayer


set_option autoImplicit false
open ThreeSum ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskDecode
theorem _root_.solution {L k m : ℕ} (hm : m ∈ enumerateLayer L k) :
    (decode L m).card = k := by
  have h := (mem_enumerateLayer L k m).mp hm
  rw [decode_card h.1, h.2]
end ThreeSum.MaskDecode
