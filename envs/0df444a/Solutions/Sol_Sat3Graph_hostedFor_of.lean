-- Prove2me | solution 1 for Sat3Graph.hostedFor_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:00:47.579206+00:00
-- url     : https://prove2.me/submissions/88f3aa1e-4e8d-4d17-8848-d0aaa42a9bdc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Sat3Graph_Defs
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_GraphProblems_Read
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_Sat3Graph_Host
import Theorems.Thm_Sat3Graph_outputs_of_simulates
import Theorems.Thm_GraphProblems_length_codeWith
import Theorems.Thm_GraphProblems_stMatrixLength
import Theorems.Thm_SplitSat_exists_simulates


set_option autoImplicit false
section
section
open Sat3Graph
open Groundwork Groundwork.Prog GraphProblems Paper SplitSat
namespace Sat3Graph
theorem _root_.solution {Ms : StepMachine (List Bool) Bool} {p : ∀ n : ℕ, SimpleGraph (Fin n) → ℕ → Prop} {δ : ℝ} {c : ℕ} (hδ : 0 < δ)
    (hp : PolyTimeSteps Ms) (h : DecidesGraph Ms p (δ / 2) c) : HostedFor Ms p δ := by
  obtain ⟨M, q, hfin, hs⟩ := exists_simulates Ms hp
  obtain ⟨C, hC⟩ := outputs_of_simulates hs hδ c
  refine ⟨M, C, q, hfin, hs, fun n G s hsn => ?_⟩
  obtain ⟨T, b, hr, hb, hT⟩ := h n G s hsn
  refine ⟨b, hb, hC n _ b T ?_ hr hT⟩
  rw [length_codeWith stMatrixLength]
  have e : (n + 2) ^ 2 = n * n + 4 * n + 4 := by ring
  omega
end Sat3Graph
