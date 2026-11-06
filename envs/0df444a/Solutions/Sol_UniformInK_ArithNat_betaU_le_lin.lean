-- Prove2me | solution 1 for UniformInK.ArithNat.betaU_le_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:39:52.909525+00:00
-- url     : https://prove2.me/submissions/5d9e4f6f-33ec-4e61-9c26-24e486e72fed

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
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open UniformInK UniformInK.ArithNat
open Groundwork PaddedDescent PaddedDescent.F CountKSatRate ClauseBound.Alg ClauseBound.Alg.TopArith ClauseBound.TopN ClauseBound.TopN.Arith ClauseBound.ParityChecks
variable {β k K n C₀ : ℕ}
namespace UniformInK.ArithNat
theorem _root_.solution {k : ℕ} (s : ℕ) (hk : 1 ≤ k) : betaU k s + 1 ≤ 35 * k * (s + 1) := by
  unfold betaU
  nlinarith [Nat.zero_le (k * s)]
end UniformInK.ArithNat
