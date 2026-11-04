-- Prove2me | solution 1 for WeightedCache3SUM.bound_192027942
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T00:00:21.405083+00:00
-- url     : https://prove2.me/submissions/ee03c376-9182-44d2-a2cb-c0c80937728b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Race_bound

theorem solution : EndStatement.ThreeSum.SolvedInTime (96013971 / 50000000 : Rat) := Race.bound
