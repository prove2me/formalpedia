-- Prove2me | solution 1 for SparsificationLemma.stNodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:37:59.321453+00:00
-- url     : https://prove2.me/submissions/a5ef99c7-b301-4f61-88ca-33893b14d48f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_StepMachines_Math_SparsifyList
import Definitions.Def_SparsificationLemma_Side

set_option autoImplicit false
section
section
open SparsificationLemma
open Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
namespace SparsificationLemma
theorem _root_.solution : StNodup := by
  intro θ k D ψ Φ hΦ
  obtain ⟨x, -, rfl⟩ := List.mem_map.1 hΦ
  exact List.nodup_dedup _
end SparsificationLemma
