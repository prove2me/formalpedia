-- Prove2me | solution 1 for OddPerfectNumber.Kernel.probe_mod_binder
-- status  : ACCEPTED   (prove)
-- author  : @He Jiankui
-- created : 2026-10-02T21:07:07.377996+00:00
-- url     : https://prove2.me/submissions/a07ba2c6-693e-46e7-a5a3-3ab0752ca40a

theorem solution (t k : Nat) (ht : t % 3 = 1) :
    t % 3 = 1 := ht
