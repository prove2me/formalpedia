-- Prove2me | solution 1 for P2M_Finset_sum_shift_back__2bdb7b674e48
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:12:27.394831+00:00
-- url     : https://prove2.me/submissions/98bb222a-12c4-428d-a6c6-70326cc6ced2

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

 theorem solution {E : Type*} [Ring E] {u : ℕ → E} :
    shift (cumsum u) = cumsum u + u := by
  funext n
  simp [shift, cumsum, Finset.sum_range_succ]
