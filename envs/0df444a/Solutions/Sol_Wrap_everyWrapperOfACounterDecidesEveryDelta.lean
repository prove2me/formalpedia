-- Prove2me | solution 1 for Wrap.everyWrapperOfACounterDecidesEveryDelta
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:56:49.556164+00:00
-- url     : https://prove2.me/submissions/c7f88a76-2a67-4333-a1e3-117d9d807792

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Defs
import Definitions.Def_Wrap_CodingExists
import Definitions.Def_Wrap_Sim
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_Wrap_Arith
import Definitions.Def_Wrap_ArithRate
import Definitions.Def_WidthThree_Rates
import Definitions.Def_VariableBound_Paper_MainTheorem
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_VariableBound_Paper_Rename_End
import Definitions.Def_Wrap_Main
import Theorems.Thm_Wrap_decidesTM_of_wraps_counter
import Theorems.Thm_ClauseBound_Inst_Half_CertSmall_d
import Theorems.Thm_Wrap_length_encC_pad4_le
import Theorems.Thm_Wrap_wrapped_time_le


set_option autoImplicit false
section
section
open Wrap
open Turing Groundwork
open scoped NNReal
namespace Wrap
theorem _root_.solution : EveryWrapperOfACounterDecidesEveryDelta := by
  intro pre hpre M C hM N q hW δ hδ
  obtain ⟨a, d, hL⟩ := length_encC_pad4_le
  obtain ⟨c, hc⟩ := wrapped_time_le q (9 * C) C a d (δ := (δ : ℝ)) (by exact_mod_cast hδ)
  exact ⟨c, decidesTM_of_wraps_counter hpre hM hW hL hc⟩
end Wrap
