-- Prove2me | solution 1 for ThreeSum.LightSupportMark.bit_succ_of_hit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:45:23.982851+00:00
-- url     : https://prove2.me/submissions/1f4bdff7-c19c-4b3b-8bf6-e0eda0adead4

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Data.Finset.Range
import Definitions.Def_Submission_ThreeSum_LightSupportMark
import Theorems.Thm_ThreeSum_LightSupportMark_hit_succ

set_option autoImplicit false
open ThreeSum ThreeSum.LightSupportMark
open Light Finset
namespace ThreeSum.LightSupportMark
theorem _root_.solution (key valid : ℕ → ℕ) (r i : ℕ)
    (hv : valid i=1) (hk : key i=r) : bit key valid r (i+1) = 1 :=
  if_pos ((hit_succ key valid r i).mpr (Or.inr ⟨hv,hk⟩))
end ThreeSum.LightSupportMark
