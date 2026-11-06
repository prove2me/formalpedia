-- Prove2me | solution 1 for PiecesCounted.oracleFromAlgorithm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:41:18.518212+00:00
-- url     : https://prove2.me/submissions/badee53f-d853-415f-8746-2f8930ed0888

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PiecesCountedStatement
import Definitions.Def_PiecesCounted_Basic
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_PiecesCounted_Oracle
import Theorems.Thm_PiecesCounted_passOrRun_pass
import Theorems.Thm_PiecesCounted_passOrRun_run
import Theorems.Thm_Groundwork_PolyT_elim
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_Evaluator_Correct_mono
import Theorems.Thm_Groundwork_Prog_PNet_Presents_mono
import Theorems.Thm_Groundwork_Stepped_Reaches_mono
import Theorems.Thm_Groundwork_Stepped_Runs_mono
import Theorems.Thm_Groundwork_TM_Frag_Within_mono
import Theorems.Thm_Paper_Achievable_mono
import Theorems.Thm_PiecesCounted_room_le_of_length_le
import Theorems.Thm_QueryMachines_QueryMachine_Reaches_mono
import Theorems.Thm_QueryMachines_QueryMachine_Runs_mono
import Theorems.Thm_QueryMachines_QueryMachine_WithinFrom_mono
import Theorems.Thm_QueryMachines_QueryMachine_Within_mono
import Theorems.Thm_QueryMachines_stMapInRuns
import Theorems.Thm_QueryMachines_stSubstWithin
import Theorems.Thm_Sat3_DecidesTM_mono
import Theorems.Thm_Sat3_InRateTM_mono
import Theorems.Thm_Sat3_InTimeTM_mono
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PiecesCounted
open Groundwork QueryMachines
namespace PiecesCounted
theorem _root_.solution : OracleFromAlgorithm := by
  intro Q α β _ M Alg D c hC O w a T S Λ SQ b hSQ hM
  have key := stSubstWithin (Q ⊕ (List Unit × Question)) Answer Q Answer Unit α β M (passOrRun Alg) (Sum.elim O fun g => if g.1.length ≤ Λ then D.oracle g else none) O
    (Sum.elim (fun x => w x + 2) (price c)) w () a T S (max (room c Λ + 1) (SQ + 2)) b (Sum.elim w fun g => steps c g.1.length) hM ?_ ?_
  · obtain ⟨own, L, hr, hle⟩ := key
    refine ⟨own, L, QueryMachine.Runs.mono (stMapInRuns _ _ _ _ _ (fun a : α => ((), a)) (M.subst (passOrRun Alg)) O a own _ L b hr) le_rfl ?_, hle⟩
    have e : size () = 1 := rfl
    rw [e]
    omega
  · rintro (x | g) v hv
    · have hv' : O x = some v := hv
      have := hSQ x v hv'
      exact (passOrRun_pass Alg O w hv').mono le_rfl (by omega)
    · have hv' : (if g.1.length ≤ Λ then D.oracle g else none) = some v := hv
      split at hv'
      · rename_i hg
        have := room_le_of_length_le c hg
        exact (passOrRun_run O w (hC g v hv')).mono le_rfl (by omega)
      · cases hv'
  · rintro (x | g) <;> exact le_rfl
end PiecesCounted
