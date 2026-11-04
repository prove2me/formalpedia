-- Prove2me | solution 1 for ThreeSum.ColorScan.hit_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:54.200098+00:00
-- url     : https://prove2.me/submissions/f429a348-a285-4d32-80b4-ae97848e2977

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_ColorScan

set_option autoImplicit false
open ThreeSum ThreeSum.ColorScan
open ColorParameters
namespace ThreeSum.ColorScan
theorem _root_.solution {n W a b : ℕ} {x : Fin n → ℤ} (hab : a ≤ b) :
    Hit x W a → Hit x W b := by
  rintro ⟨i,hi,hlt,hx⟩
  exact ⟨i,hi,hlt.trans_le hab,hx⟩
end ThreeSum.ColorScan
