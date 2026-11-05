-- Prove2me | solution 1 for Wrap.wraps_of_coding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:07:16.262191+00:00
-- url     : https://prove2.me/submissions/5c572275-237c-4e89-91c5-ff433dc79a15

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_CountKSat_Host
import Definitions.Def_StepMachines_Prog_Stepped
import Definitions.Def_ToTuring_Closure_Basic
import Definitions.Def_ToTuring_Lib_List1b
import Definitions.Def_Wrap_Sim
import Theorems.Thm_Wrap_sim_runs
import Theorems.Thm_Wrap_Outputs_mono
import Theorems.Thm_Wrap_exists_bound
import Theorems.Thm_CountKSat_exists_tmW
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_Groundwork_length_le_len
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork CircuitLowerBound.Tab
variable {M : TM2ComputableAux Bool Bool}
namespace Wrap
theorem _root_.solution {M : TM2ComputableAux Bool Bool} (K : Coding M) {pre post : List Bool → List Bool} (hpre : PolyT pre) (hpost : PolyT post) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ i, Finite (N.tm.Γ i)) ∧ Wraps M pre post N q := by
  have := sim_isPolyT K hpre hpost
  obtain ⟨N, q₀, hfin, hN⟩ := CountKSat.exists_tmW (sim K pre post)
  obtain ⟨-, c, -, hc⟩ := hpre
  obtain ⟨q, hq⟩ := exists_bound q₀ K.a c
  refine ⟨N, q, hfin, fun x y t h => ?_⟩
  have hp : (pre x).length ≤ c * (3 * x.length + 2 + 1) ^ c := by
    have := hc x
    rw [len_bools x] at this
    exact (length_le_len _).trans this
  exact Outputs.mono (hN x t _ (post y) (sim_runs K pre post h)) (hq t x.length _ hp)
end Wrap
