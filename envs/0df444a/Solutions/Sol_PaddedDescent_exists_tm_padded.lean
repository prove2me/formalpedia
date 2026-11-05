-- Prove2me | solution 1 for PaddedDescent.exists_tm_padded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:37:48.532551+00:00
-- url     : https://prove2.me/submissions/2705d502-0d14-44f5-8588-8fbb08f7aceb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_PaddedDescent_Host
import Definitions.Def_ToTuring_Lib_Nat1b
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_PaddedDescent_Pad
import Theorems.Thm_PaddedDescent_padM_runs
import Theorems.Thm_PaddedDescent_pad_bound
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_P2M_PaddedDescent_exists_tm__adb177e912aa
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
open PaddedDescent
open Groundwork Sat3 Turing
variable {e : List Bool → ℕ} {A : List Bool × List Unit → Bool}
namespace PaddedDescent
theorem _root_.solution (he : PolyT e) (hA : PolyT A) :
    ∃ (N : TM2ComputableAux Bool Bool) (q : ℕ), (∀ k, Finite (N.tm.Γ k)) ∧
      ∀ x : List Bool,
        Nonempty (TM2OutputsInTime N.tm (x.map N.inputAlphabet.invFun)
          (some ([A (x, pad (e x))].map N.outputAlphabet.invFun)) (q * (x.length + 2 ^ e x + 1) ^ q)) := by
  have := padM_isPolyT he hA
  obtain ⟨N, q, hfin, hN⟩ := exists_tm' (padM e A)
  refine ⟨N, q * 4 ^ (q + 1) + (q + 1), hfin, fun x => ?_⟩
  obtain ⟨ev⟩ := hN x _ _ _ (padM_runs e A x)
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans (pad_bound q x.length (e x))⟩⟩
end PaddedDescent
