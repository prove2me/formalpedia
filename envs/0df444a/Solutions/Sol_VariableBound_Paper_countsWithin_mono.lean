-- Prove2me | solution 1 for VariableBound.Paper.countsWithin_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T01:36:36.616714+00:00
-- url     : https://prove2.me/submissions/7634c1f3-3f49-40a5-9c04-e1c04e2e225d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Forms
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)
namespace VariableBound.Paper
theorem _root_.solution {M : TM2ComputableAux Bool Bool} {k n : ℕ} {φ : CNF n} {t t' : ℕ} (h : CountsWithin M k φ t) (ht : t ≤ t') : CountsWithin M k φ t' := by
  obtain ⟨ev⟩ := h
  exact ⟨⟨ev.toEvalsTo, ev.steps_le_m.trans ht⟩⟩
end VariableBound.Paper
