-- Prove2me | solution 1 for P2M_Eight_delta__le_fd4e6e087c27
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:13:37.588939+00:00
-- url     : https://prove2.me/submissions/3d319d40-c7b9-4977-929f-c44d78920fe7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_Level_End
import Definitions.Def_Eight_SecProof_Network
import Definitions.Def_CountKSat_Value
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_Eight_SecProof_Proof
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog Paper
namespace Eight
theorem _root_.solution {δ M : ℝ} (hδ1 : δ ≤ 1) (hM : 1 ≤ M) : δ / (3 * M) ≤ 1 / 3 := by
  rw [div_le_iff₀ (by linarith)]
  linarith
end Eight
