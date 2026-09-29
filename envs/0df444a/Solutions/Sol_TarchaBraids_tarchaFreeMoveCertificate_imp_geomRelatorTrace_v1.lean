-- Prove2me | solution 1 for TarchaBraids.tarchaFreeMoveCertificate_imp_geomRelatorTrace_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T10:54:49.498434+00:00
-- url     : https://prove2.me/submissions/1df344b6-f9bd-46a0-94c1-8825204fd104

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1
import Definitions.Def_TarchaBraids_TarchaFreeMoveCertificate_v1
import Theorems.Thm_TarchaBraids_adjacent_braid_word_is_one_step_trace_v1
import Theorems.Thm_TarchaBraids_far_comm_word_is_one_step_trace_v1

open BraidsLinksMCG TarchaBraids

private theorem freeMoveTrace_eq {n : ℕ} {x y : FreeGroup (Fin (n - 1))}
    (hxy : x = y) (t : GeomRelatorTrace n x) :
    GeomRelatorTrace n y := by
  cases hxy
  exact t

private theorem freeMoveTrace_mul {n : ℕ} {x y : FreeGroup (Fin (n - 1))}
    (hx : GeomRelatorTrace n x) (hy : GeomRelatorTrace n y) :
    GeomRelatorTrace n (x * y) := by
  induction hx with
  | nil =>
      simpa using hy
  | @step w u r hx hr ih =>
      simpa [mul_assoc] using
        (GeomRelatorTrace.step (n := n) (w := w * y) (u := u) (r := r)
          ih hr)

theorem solution
    {n : ℕ} {w : FreeGroup (Fin (n - 1))}
    (c : TarchaFreeMoveCertificate n w) :
    GeomRelatorTrace n w := by
  induction c with
  | nil => exact GeomRelatorTrace.nil
  | @freeEq x y h c ih => exact freeMoveTrace_eq h ih
  | @contextual w u r c hr ih => exact GeomRelatorTrace.step ih hr
  | @mul x y c₁ c₂ ih₁ ih₂ => exact freeMoveTrace_mul ih₁ ih₂
  | @far i j hij => exact far_comm_word_is_one_step_trace_v1 i j hij
  | @adjacent i j hji => exact adjacent_braid_word_is_one_step_trace_v1 i j hji
