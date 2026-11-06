-- Prove2me | solution 1 for P2M_pp__deriv_0c521294d559
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:30:02.083723+00:00
-- url     : https://prove2.me/submissions/c07400ec-c2f0-41e0-a4d0-263986f05aba

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

theorem solution (a x : ℝ) : HasDerivAt (pp' a) (a ^ 2 * 2) x := by
  change HasDerivAt (fun y : ℝ => a ^ 2 * (2 * (y + 1))) (a ^ 2 * 2) x
  simpa [add_comm] using
    ((((hasDerivAt_id x).const_add 1).const_mul 2).const_mul (a ^ 2))
