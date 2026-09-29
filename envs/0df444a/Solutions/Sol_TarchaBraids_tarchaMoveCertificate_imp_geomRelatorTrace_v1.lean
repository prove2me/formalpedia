-- Prove2me | solution 1 for TarchaBraids.tarchaMoveCertificate_imp_geomRelatorTrace_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-24T09:58:38.844982+00:00
-- url     : https://prove2.me/submissions/d653cfd4-67c4-4069-a7bf-be7193da5bbd

import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_TarchaBraids_GeomRelatorTrace_v1
import Definitions.Def_TarchaBraids_TarchaMoveCertificate_v1
import Theorems.Thm_TarchaBraids_adjacent_braid_word_is_one_step_trace_v1
import Theorems.Thm_TarchaBraids_far_comm_word_is_one_step_trace_v1

open BraidsLinksMCG TarchaBraids

theorem solution
    {n : ℕ} {w : FreeGroup (Fin (n - 1))}
    (c : TarchaMoveCertificate n w) :
    GeomRelatorTrace n w := by
  induction c with
  | nil => exact GeomRelatorTrace.nil
  | @step w u r c hr ih =>
      exact GeomRelatorTrace.step ih hr
  | @far i j hij =>
      exact far_comm_word_is_one_step_trace_v1 i j hij
  | @adjacent i j hji =>
      exact adjacent_braid_word_is_one_step_trace_v1 i j hji
