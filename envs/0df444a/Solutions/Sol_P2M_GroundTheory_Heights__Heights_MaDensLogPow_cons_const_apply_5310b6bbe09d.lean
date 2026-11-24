-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MaDensLogPow_cons_const_apply_5310b6bbe09d
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T04:28:16.258936+00:00
-- url     : https://prove2.me/submissions/65c14c88-8756-4fb8-a257-7f9cb01ea37a

import Mathlib


theorem solution {n : ℕ} (A₀ H : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) ℂ) (k : Fin (n + 1 + 1)) :
    (Fin.cons A₀ (fun _ : Fin (n + 1) => H) : Fin (n + 1 + 1) → _) k = if k = 0 then A₀ else H := by
  refine Fin.cases ?_ (fun j => ?_) k <;> simp
