-- Prove2me | solution 1 for OddPerfectNumber.Kernel.dris_five_probe_layout
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T14:28:23.703712+00:00
-- url     : https://prove2.me/submissions/c32a4819-841f-4299-829e-f50c6a5965b7

theorem solution (a b : Nat) (h : a = b) : b = a := by
  exact h.symm
