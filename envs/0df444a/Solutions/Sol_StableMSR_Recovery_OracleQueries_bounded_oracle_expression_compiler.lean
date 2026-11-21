-- Prove2me | solution 1 for StableMSR.Recovery.OracleQueries.bounded_oracle_expression_compiler
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T20:28:05.966418+00:00
-- url     : https://prove2.me/submissions/6661e08c-8d23-4322-bf24-8401b1c46d11

import Theorems.Thm_StableMSR_Recovery_OracleQueries_oracle_query_primitives
import Theorems.Thm_StableMSR_Recovery_OracleQueries_axis_sum_machine
import Definitions.Def_StableMSR_OracleQueries
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open Polynomial
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

theorem solution (f : Term) (h : Form f) : Engine f := by
  induction h with
  | const z => exact oracle_query_primitives.1 z
  | var i => exact oracle_query_primitives.2.1 i
  | size a => exact oracle_query_primitives.2.2.1 a
  | bin p _ _ ih jh => exact oracle_query_primitives.2.2.2.1 p _ _ ih jh
  | branch _ _ _ ih jh kh => exact oracle_query_primitives.2.2.2.2 _ _ _ ih jh kh
  | rename _ σ ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨p,?_⟩
    intro b src hb hs
    obtain ⟨cmd,hc⟩ := hp b (src ∘ σ) hb (fun i=>hs (σ i))
    exact ⟨cmd,fun x s ρ hr reads=>hc x s (ρ ∘ σ) hr (fun i=>reads (σ i))⟩
  | total a _ ih => exact axis_sum_machine a _ ih
