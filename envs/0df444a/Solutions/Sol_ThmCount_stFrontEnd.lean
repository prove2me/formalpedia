-- Prove2me | solution 1 for ThmCount.stFrontEnd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:16:33.53122+00:00
-- url     : https://prove2.me/submissions/2741d27b-0543-42ab-b45c-cb05790c8bb7

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThmCount_Defs
import Definitions.Def_Wrap_FrontEnd
import Definitions.Def_WidthK_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Mathlib.Tactic
import Definitions.Def_ThmCount_FrontEnd
import Theorems.Thm_ThmCount_frontEnd_enc
import Theorems.Thm_ThmCount_frontEnd_polyT
import Theorems.Thm_Wrap_frontEnd_enc
import Theorems.Thm_Wrap_frontEnd_polyT


set_option autoImplicit false
section
section
section
open ThmCount
open Groundwork Groundwork.Decode
namespace ThmCount
theorem _root_.solution : StFrontEnd := ⟨frontEnd, frontEnd_polyT, fun _ _ hφ => frontEnd_enc hφ.1⟩
end ThmCount
