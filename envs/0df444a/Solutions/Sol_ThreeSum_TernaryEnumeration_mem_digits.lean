-- Prove2me | solution 1 for ThreeSum.TernaryEnumeration.mem_digits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T06:24:22.996043+00:00
-- url     : https://prove2.me/submissions/2c2ddc7a-2583-4ea4-8525-dfe4f94222a5

import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic
import Definitions.Def_Submission_ThreeSum_TernaryEnumeration

set_option autoImplicit false
open ThreeSum ThreeSum.TernaryEnumeration
namespace ThreeSum.TernaryEnumeration
theorem _root_.solution {d t : ℕ} : d ∈ digits t ↔ d < 3 ∧ d ≤ t := by
  simp [digits]
end ThreeSum.TernaryEnumeration
