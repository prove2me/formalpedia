-- Prove2me | solution 1 for UniformInK.stBetaU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:48:42.278819+00:00
-- url     : https://prove2.me/submissions/c74a4357-8d7e-4a2d-b0c5-78f76d265597

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_ArithDefs
import Definitions.Def_ClauseBound_ParityChecks_Sizes
import Definitions.Def_ClauseBound_ParityChecks_ArithAux
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_TopN_Arith
import Definitions.Def_ClauseBound_Alg_TopArith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_UniformInK_Top_ArithNat
import Theorems.Thm_UniformInK_ArithNat_k_le_betaU
import Theorems.Thm_UniformInK_ArithNat_b_le_DU
import Theorems.Thm_UniformInK_ArithNat_betaU_le_lin
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK
namespace UniformInK
theorem _root_.solution : StBetaU := fun k s hk => ⟨ArithNat.k_le_betaU k s, ArithNat.b_le_DU s hk, ArithNat.betaU_le_lin s hk⟩
end UniformInK
