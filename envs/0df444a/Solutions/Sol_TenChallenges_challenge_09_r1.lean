-- Prove2me | solution 1 for TenChallenges.challenge_09_r1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T02:38:13.511175+00:00
-- url     : https://prove2.me/submissions/398e8615-cc79-4d95-a5a7-a7afa447245f

import Theorems.Thm_TenChallenges_challenge_09_r6
import Mathlib.Tactic.NormNum

set_option autoImplicit false

theorem solution : TenChallenges.statement_09 1 := by
  intro U _ F huc hnd
  obtain ⟨x, hx⟩ := TenChallenges.challenge_09_r6 F huc hnd
  refine ⟨x, le_trans ?_ hx⟩
  norm_num
