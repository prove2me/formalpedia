-- Prove2me | solution 1 for PaddedDescent.F.stLayersE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:36:16.19178+00:00
-- url     : https://prove2.me/submissions/3d8a6222-51e2-48d9-9747-fde33cecb9d6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkSums
import Definitions.Def_PaddedDescent_F_Interfaces
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Definitions.Def_PaddedDescent_F_MarkLayers
import Theorems.Thm_PaddedDescent_F_Mark_ev_layersE

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F
theorem _root_.solution : StLayersE := fun _ _ _ _ _ hw hR hev => Mark.ev_layersE hw hR hev
end PaddedDescent.F
