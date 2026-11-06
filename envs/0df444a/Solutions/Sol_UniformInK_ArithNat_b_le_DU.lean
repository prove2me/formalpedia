-- Prove2me | solution 1 for UniformInK.ArithNat.b_le_DU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:43:42.347638+00:00
-- url     : https://prove2.me/submissions/137b41ab-bf67-49c9-a872-fd884cc86edb

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
theorem _root_.solution {k : ℕ} (s : ℕ) (hk : 1 ≤ k) : betaU k s + 3 ≤ 2 ^ betaU k s := by
  have h3 : 3 ≤ betaU k s := by
    unfold betaU
    nlinarith [Nat.zero_le (k * s)]
  obtain ⟨t, ht⟩ : ∃ t, betaU k s = t + 3 := ⟨betaU k s - 3, by omega⟩
  have h : t + 1 ≤ 2 ^ t := Nat.lt_two_pow_self
  rw [ht, pow_add]
  omega
end UniformInK.ArithNat
