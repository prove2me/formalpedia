-- Prove2me | solution 1 for SparsificationLemma.StepSparsify.sparsABC
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:07.33078+00:00
-- url     : https://prove2.me/submissions/6ca13720-583f-46a0-b592-2d48360fbe80

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
import Theorems.Thm_SparsificationLemma_Cal_sparsABC
import Theorems.Thm_SparsificationLemma_Cal_stAlpha
import Theorems.Thm_SparsificationLemma_Cal_stDegLe
import Theorems.Thm_SparsificationLemma_Cal_stYLe
import Theorems.Thm_SparsificationLemma_stNodup


set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.StepSparsify
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate SparsificationLemma.Cal
namespace SparsificationLemma.StepSparsify
theorem _root_.solution : SparsABC := Cal.sparsABC stNodup stAlpha stYLe stDegLe
end SparsificationLemma.StepSparsify
