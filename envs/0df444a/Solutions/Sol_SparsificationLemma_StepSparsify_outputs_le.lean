-- Prove2me | solution 1 for SparsificationLemma.StepSparsify.outputs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:08:28.110709+00:00
-- url     : https://prove2.me/submissions/54163b28-2af1-47d2-9b2a-e1074929a4ee

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_SparsificationLemma_Cal_sparsABC
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.StepSparsify
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate SparsificationLemma.Cal
variable {k n : ℕ} {ε : ℚ} {φ : PFml}
namespace SparsificationLemma.StepSparsify
theorem _root_.solution (hk : 3 ≤ k) (h0 : 0 < ε) (h1 : ε ≤ 1) (hφ : IsKCNF k n φ) : ((sparsify k n ε φ).length : ℝ) ≤ (2 : ℝ) ^ ((ε : ℝ) * (n : ℝ)) :=
  (sparsABC k n ε φ hk h0 h1 hφ).2.1
end SparsificationLemma.StepSparsify
