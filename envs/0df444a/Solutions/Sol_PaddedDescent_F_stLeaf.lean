-- Prove2me | solution 1 for PaddedDescent.F.stLeaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:11:04.495356+00:00
-- url     : https://prove2.me/submissions/3c421a02-8961-4646-8a6b-03a022a5b899

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Step
import Definitions.Def_SparsifyWidthK_SetAlg
import Definitions.Def_SparsifyWidthK_Thresholds
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_PaddedDescent_F_MarkDeg
import Theorems.Thm_PaddedDescent_F_Mark_Deg_leaf_spec

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F
theorem _root_.solution : StLeaf := fun k _ n ψ hτ hψ x hx =>
  ⟨(Mark.Deg.leaf_spec hτ k n ψ hψ x hx).2.1, (Mark.Deg.leaf_spec hτ k n ψ hψ x hx).2.2⟩
end PaddedDescent.F
