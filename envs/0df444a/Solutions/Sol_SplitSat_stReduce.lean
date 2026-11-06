-- Prove2me | solution 1 for SplitSat.stReduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:38.611537+00:00
-- url     : https://prove2.me/submissions/5db6840e-08f0-4247-a6ce-0019deba98a9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Walk
import Definitions.Def_CountKSat_InOut
import Definitions.Def_SplitSat_Reader
import Theorems.Thm_SplitSat_decides_of_decidesW
import Theorems.Thm_SplitSat_stReduceCore


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Paper CountKSat Eight.ViaGrouping
namespace SplitSat
theorem _root_.solution : StReduce := fun k hk δ hδ τ Dd B Sk hsp D δ₃ c h0 hδB hD => by
  obtain ⟨c', h⟩ := stReduceCore k hk δ hδ τ Dd B Sk hsp D δ₃ c h0 hδB hD
  exact ⟨c', decides_of_decidesW (by omega) h⟩
end SplitSat
