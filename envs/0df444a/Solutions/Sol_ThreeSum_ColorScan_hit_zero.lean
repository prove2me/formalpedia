-- Prove2me | solution 1 for ThreeSum.ColorScan.hit_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:53.026111+00:00
-- url     : https://prove2.me/submissions/49870f82-28ff-4ceb-951e-e5dde77fc297

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_ColorScan

set_option autoImplicit false
open ThreeSum ThreeSum.ColorScan
open ColorParameters
namespace ThreeSum.ColorScan
theorem _root_.solution {n W : ℕ} (x : Fin n → ℤ) : ¬ Hit x W 0 := by
  rintro ⟨i,hi,hlt,_⟩
  omega
end ThreeSum.ColorScan
