-- Prove2me | solution 1 for StableMSR.Recovery.Compiler.BoundedSum.bounded_sum_compiler
-- status  : ACCEPTED   (prove)
-- author  : @lreyzin
-- created : 2026-11-20T18:09:41.241062+00:00
-- url     : https://prove2.me/submissions/ffac740b-6295-455d-a4d6-0411d86775de

import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_elementary_register_engines
import Theorems.Thm_StableMSR_Recovery_Compiler_BoundedSum_bounded_sum_register_engine
import Definitions.Def_StableMSR_BoundedSumRAM
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.Compiler.BoundedSum
open Polynomial
set_option maxHeartbeats 1600000
open scoped Classical

theorem solution (f : Env→ℕ) (h : Form f) : Engine f := by
  obtain ⟨lit,var,bin⟩ := elementary_register_engines
  induction h with
  | lit a => exact lit a
  | var i => exact var i
  | bin o _ _ ih jh => exact bin o _ _ ih jh
  | @rename f h σ ih =>
    obtain ⟨p,hp⟩ := ih
    refine ⟨p,fun src b small => ?_⟩
    obtain ⟨c,hc⟩ := hp (src ∘ σ) b (fun i=>small (σ i))
    exact ⟨c,fun n d s ρ M bound reads => hc n d s (ρ ∘ σ) M (fun i=>bound (σ i)) (fun i=>reads (σ i))⟩
  | sum _ _ ih jh => exact bounded_sum_register_engine _ _ ih jh

