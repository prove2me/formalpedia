-- Prove2me | solution 1 for ThreeSum.TernaryAddressDecode.word_address
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:40.715774+00:00
-- url     : https://prove2.me/submissions/5a75eee0-1985-4614-83b0-4daab79b5c2d

import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_TernaryAddressDecode
import Theorems.Thm_ThreeSum_TernaryCodeSemantics_digit_eq


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryAddressDecode
open TernaryJointType TernaryCodeSemantics
namespace ThreeSum.TernaryAddressDecode
theorem _root_.solution {N : ℕ} (W : TritWord N) : word N (address W)=W := by
  funext i
  apply Fin.ext
  exact digit_eq W i
end ThreeSum.TernaryAddressDecode
