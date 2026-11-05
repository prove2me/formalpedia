-- Prove2me | solution 1 for VariableBound.CorrectB.useMD_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:17:27.525607+00:00
-- url     : https://prove2.me/submissions/a879a194-bb3e-41e7-ab36-2f1b3defc1f2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Top_Defs
import Definitions.Def_VariableBound_Top_CorrectB
import Theorems.Thm_Groundwork_Decode_length_toN
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open VariableBound VariableBound.CorrectB
open Groundwork Groundwork.Prog PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks UniformInK
namespace VariableBound.CorrectB
theorem _root_.solution (hA : StAllOccU) (hD : StDecM) {Idx : Type} [Enc Idx] (S : Solver Idx) (k : ℕ) (pick : U → U × Idx) (slU : U → U) {n : ℕ} (φ : Sat3.CNF n)
    (hk : 1 ≤ k) (hφ : SatK.IsKCNF k φ) :
    useMD S pick slU (SatM.enc k φ) = true ↔
      SatM.AllOccur φ ∧ 1 ≤ φ.length ∧ eM S pick (SatM.enc k φ) ≤ eD S pick slU (SatM.enc k φ) := by
  unfold useMD
  rw [(hD k n φ hk hφ.1).2, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hA k n φ hk hφ, Decode.length_toN, and_assoc]
end VariableBound.CorrectB
