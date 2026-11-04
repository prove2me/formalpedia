-- Prove2me | solution 1 for ThreeSum.TernarySignedModes.carryAt_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:42:20.060581+00:00
-- url     : https://prove2.me/submissions/deb06eaf-e9fd-46fd-8f4d-b95ebdd4d3e3

import Definitions.Def_Submission_ThreeSum_TernarySignedReduction
import Mathlib.Data.Int.Lemmas
import Definitions.Def_Submission_ThreeSum_TernarySignedModes

set_option autoImplicit false
open ThreeSum ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset
namespace ThreeSum.TernarySignedModes
theorem _root_.solution {J : ℕ} (c : CarryWord J) (j : ℕ) :
    0 ≤ carryAt c j ∧ carryAt c j ≤ 1 := by
  unfold carryAt
  split_ifs with h
  · have hh := (c ⟨j,h⟩).isLt
    constructor <;> omega
  · norm_num
end ThreeSum.TernarySignedModes
