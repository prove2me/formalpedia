-- Prove2me | solution 1 for SatFree.inTimeRand_of_inTime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:10:14.73604+00:00
-- url     : https://prove2.me/submissions/c66fa26d-5005-4535-a8e4-a3142f5f0454

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_KSatFreeCodeStatement
import Mathlib.Tactic
import Definitions.Def_FreeCode_Random
import Theorems.Thm_SatFree_deterministicIsRandomized
import Theorems.Thm_SatFree_decidesRandTM_mono

set_option autoImplicit false
section
section
open SatFree
open Turing
open Sat3 (CNF Satisfiable)
open scoped NNReal ENNReal
namespace SatFree
theorem _root_.solution {p : ℝ} (hp : 0 ≤ p) {k : ℕ} {δ : ℝ≥0} (h : InTime k δ) : InTimeRand p k δ := by
  obtain ⟨M, c, hfin, h⟩ := h
  refine ⟨M, c, 0, 0, le_rfl, hfin, ?_⟩
  have hr : (fun n : ℕ => ⌊((0 : ℕ) : ℝ) * (2 : ℝ) ^ (((0 : ℚ) : ℝ) * n)⌋₊) = fun _ => 0 := by
    funext n
    simp
  rw [hr]
  exact decidesRandTM_mono hp (deterministicIsRandomized k M _ h)
end SatFree
