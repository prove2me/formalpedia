-- Prove2me | solution 1 for SatFree.decidesRandTM_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:13.781243+00:00
-- url     : https://prove2.me/submissions/b3452152-e83a-49d6-b24d-eec7bcb80fa9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random

set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution {p p' : ℝ} (hp : p ≤ p') {k : ℕ} {M : TM2ComputableAux Bool Bool} {r t : ℕ → ℕ} (h : DecidesRandTM p k M r t) :
    DecidesRandTM p' k M r t := fun n φ hφ => by
  obtain ⟨h1, b, hb, h2⟩ := h n φ hφ
  refine ⟨h1, b, hb, le_trans ?_ h2⟩
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end SatFree
