-- Prove2me | solution 1 for SplitSat.stReduceCore
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:10:32.515448+00:00
-- url     : https://prove2.me/submissions/6283bfa0-f6c3-4ad5-a066-39dbc505fd66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Leaf
import Definitions.Def_SplitSat_Sizes
import Mathlib.Tactic
import Definitions.Def_SplitSat_Walk
import Theorems.Thm_SplitSat_reduceCore_decides

set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK Groundwork.Sparsify WidthK.Prog UniformInK Paper Eight.Width
namespace SplitSat
theorem _root_.solution : StReduceCore := fun _ hk _ hδ _ _ _ _ hsp D _ _ h0 hδB hD => reduceCore_decides hk hδ hsp D h0 hδB hD
end SplitSat
