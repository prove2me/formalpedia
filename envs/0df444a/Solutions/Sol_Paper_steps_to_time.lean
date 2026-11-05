-- Prove2me | solution 1 for Paper.steps_to_time
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T17:09:13.209984+00:00
-- url     : https://prove2.me/submissions/1abdacf7-f811-4cda-8306-82d88d23e5f5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmEveryDeltaStatement
import Definitions.Def_StepMachineStatements
import Definitions.Def_ToTuring_PolyT
import Definitions.Def_ToTuring_Machine_EndTM
import Definitions.Def_Paper_SecNetworks_Model
import Theorems.Thm_Groundwork_inTimeTM_of_machine


set_option autoImplicit false
section
section
open Paper
open Groundwork
namespace Paper
theorem _root_.solution {δ : ℝ} (hδ : 0 < δ) (M : StepMachine (List Bool) Bool) (hM : PolyTimeSteps M)
    (h : DecidesInSteps M (δ / 2)) : Sat3.DecidedInTime δ := by
  obtain ⟨hM⟩ := hM
  obtain ⟨c, hc⟩ := h
  obtain ⟨N, C, hfin, hN⟩ := inTimeTM_of_machine (δ := ⟨δ, hδ.le⟩) hδ M c hc
  refine ⟨N, C, hfin, fun n φ hφ => ?_⟩
  obtain ⟨b, hb, ev⟩ := hN n φ hφ
  exact ⟨b, _, hb, Nat.floor_le (by positivity), ev⟩
end Paper
