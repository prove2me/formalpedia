-- Prove2me | solution 1 for ShiQMACenteredGap.biasIter_standard
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-10-01T01:13:00.333536+00:00
-- url     : https://prove2.me/submissions/842a204b-5a7b-4bfe-a453-8d5def419866

import Definitions.Def_ShiQMACenteredGap

set_option autoImplicit false
open ShiQMACenteredGap ShiQMAErrorIteration

theorem solution (r : Nat) :
    biasIter (1 / 6) r = 1 / 2 - error r := by
  induction r with
  | zero => norm_num [biasIter, error]
  | succ r ih =>
    simp only [biasIter, ih, error, biasStep, majorityError]
    ring
