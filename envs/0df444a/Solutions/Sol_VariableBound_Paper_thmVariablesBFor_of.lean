-- Prove2me | solution 1 for VariableBound.Paper.thmVariablesBFor_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:10.304432+00:00
-- url     : https://prove2.me/submissions/c7e57e38-5b36-407a-8abd-798ecd2636d6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_MainTheoremFormsStatement
import Definitions.Def_VariableBound_Paper_Arith
import Definitions.Def_UniformInKStatement
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_WidthK_Decode
import Definitions.Def_VariableBound_Paper_Forms
import Theorems.Thm_VariableBound_Paper_countsWithin_mono
import Theorems.Thm_VariableBound_Paper_boundNK_le


set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)
namespace VariableBound.Paper
theorem _root_.solution {M : TM2ComputableAux Bool Bool} {C : ℕ} (h : SatM.CountsTMN M (SatM.boundNK (SatK.rN 1 (1 / 2)) C)) : ThmVariablesBFor M (3 * C) :=
  fun k n φ hk hn hφ => countsWithin_mono (h k n φ hk (by omega) hφ) (boundNK_le C hk hn)
end VariableBound.Paper
