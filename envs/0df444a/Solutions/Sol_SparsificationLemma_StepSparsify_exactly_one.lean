-- Prove2me | solution 1 for SparsificationLemma.StepSparsify.exactly_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:59.4982+00:00
-- url     : https://prove2.me/submissions/6aca667d-528a-40ea-a9f0-a8be3b37a3ee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_StepSparsifyDefs
import Definitions.Def_SparsificationLemma_Nodes
import Definitions.Def_SparsificationLemma_One
import Definitions.Def_SparsificationLemma_Side
import Definitions.Def_SparsificationLemma_Len
import Definitions.Def_SparsificationLemma_Cal_Main
import Definitions.Def_SparsificationLemma_Cal_Alpha
import Definitions.Def_SparsificationLemma_Cal_Real
import Definitions.Def_SparsificationLemma_Cal_Beta
import Definitions.Def_SparsificationLemma_Cal_Facts
import Definitions.Def_SparsificationLemma_Cal_Thr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_StepSparsify
import Theorems.Thm_SparsificationLemma_StepSparsify_sparsABC
import Theorems.Thm_SparsificationLemma_Cal_sparsABC


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.StepSparsify
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate SparsificationLemma.Cal
variable {k n : ℕ} {ε : ℚ} {φ : PFml}
namespace SparsificationLemma.StepSparsify
theorem _root_.solution (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) (hφ : IsKCNF k n φ) : ∀ b, ExactlyOne b φ (sparsify k n ε φ) :=
  (sparsABC k n ε φ hk h0 h1 hφ).2.2.1
end SparsificationLemma.StepSparsify
