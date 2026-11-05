-- Prove2me | solution 1 for UniformInK.End.one_le_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T03:08:36.036297+00:00
-- url     : https://prove2.me/submissions/54bddb97-6964-4798-947f-93be3165a8c3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Top_Defs
import Definitions.Def_ClauseBound_Both_End
import Definitions.Def_UniformInK_Top_End
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open UniformInK UniformInK.End
open Groundwork Turing PaddedDescent PaddedDescent.F CountKSat CountKSatRate ClauseBound.Alg ClauseBound.TopN ClauseBound.ParityChecks ClauseBound.Both.End
namespace UniformInK.End
theorem _root_.solution {n : ℕ} {φ : Sat3.CNF n} (hn : 1 ≤ n) (ho : SatM.AllOccur φ) : 1 ≤ φ.length := by
  obtain ⟨c, hc, _⟩ := ho ⟨0, hn⟩
  exact List.length_pos_of_mem hc
end UniformInK.End
