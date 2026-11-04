-- Prove2me | solution 1 for ThreeSum.LightTernaryTensorScatter.address_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:01:35.910342+00:00
-- url     : https://prove2.me/submissions/45062837-a66f-4ae7-bb4a-f4f53bec9037

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightTernaryTensorScatter

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryTensorScatter
open Light
set_option maxHeartbeats 1800000
namespace ThreeSum.LightTernaryTensorScatter
theorem _root_.solution {W a b q r : ℕ} (hq : q<W) (hr : r<W)
    (h : a*W+q=b*W+r) : a=b ∧ q=r := by
  have hw : 0<W := by omega
  have ha : a*W+q<(a+1)*W := by nlinarith
  have hb : b*W+r<(b+1)*W := by nlinarith
  have hab : a=b := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with hh | hh
    · have := Nat.mul_le_mul_right W (by omega : a+1≤b)
      omega
    · have := Nat.mul_le_mul_right W (by omega : b+1≤a)
      omega
  exact ⟨hab,by subst b; omega⟩
end ThreeSum.LightTernaryTensorScatter
