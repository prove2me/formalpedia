-- Prove2me | solution 1 for ThreeSum.MaskDecode.decoded_downset_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:16:38.956847+00:00
-- url     : https://prove2.me/submissions/4c2dc8f5-191e-4fa0-b2c4-db7dac37369c

import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_MaskDecode
import Theorems.Thm_ThreeSum_MaskDecode_decode_subsetMask
import Theorems.Thm_ThreeSum_SubsetAddress_subsetMask_mem_enumeration


set_option autoImplicit false
open ThreeSum ThreeSum.MaskDecode
open Finset
open scoped BigOperators
open SubsetAddress
namespace ThreeSum.MaskDecode
theorem _root_.solution {L cut : ℕ} (s : Finset (Fin L)) (hs : s.card ≤ cut) :
    s ∈ (enumerateDownset L cut).map (decode L) := by
  exact List.mem_map.mpr ⟨subsetMask s, subsetMask_mem_enumeration hs, decode_subsetMask s⟩
end ThreeSum.MaskDecode
