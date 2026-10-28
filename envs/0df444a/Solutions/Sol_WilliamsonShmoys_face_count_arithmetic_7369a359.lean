-- Prove2me | solution 1 for WilliamsonShmoys.face_count_arithmetic_7369a359
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T12:02:42.672312+00:00
-- url     : https://prove2.me/submissions/127b5b4e-c314-445c-99b5-c659f05e15ba

import Mathlib

set_option autoImplicit false

theorem solution
    (n e : Nat)
    (hCard : 3 <= n)
    (hEdges : e + 6 = 3 * n) :
    Exists (fun f : Nat =>
      n + f = e + 2 /\
      3 * f = 2 * e) := by
  refine Exists.intro (2 * n - 4) ?_
  constructor <;> omega