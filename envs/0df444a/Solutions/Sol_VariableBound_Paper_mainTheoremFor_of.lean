-- Prove2me | solution 1 for VariableBound.Paper.mainTheoremFor_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:18:18.873928+00:00
-- url     : https://prove2.me/submissions/7138bdf0-9402-4226-bdfd-16f2033c9695

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_VariableBound_Paper_boundBothK_le
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.Paper
open MainTheoremForms Turing
open Sat3 (CNF)
namespace VariableBound.Paper
theorem _root_.solution {M : TM2ComputableAux Bool Bool} {C : ℕ}
    (h : ∀ (k n : ℕ) (φ : CNF n), 1 ≤ k → 1 ≤ n → SatK.IsKCNF k φ → SatM.AllOccur φ →
      CountsWithin M k φ (SatM.boundBothK (SatK.rN 1 (1 / 2)) (SatM.rPow (1 / 2)) C k n φ.length)) : MainTheoremFor M (3 * C) :=
  fun k n φ hk hφ hm hn hocc => countsWithin_mono (h k n φ hk (by omega) hφ hocc) (boundBothK_le C hk hm hn)
end VariableBound.Paper
