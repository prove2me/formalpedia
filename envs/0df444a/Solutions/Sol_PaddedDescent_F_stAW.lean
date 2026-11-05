-- Prove2me | solution 1 for PaddedDescent.F.stAW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:19:07.452218+00:00
-- url     : https://prove2.me/submissions/b3186e29-82d1-4e01-af8a-3c71d72c9377

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_ArithSched
import Definitions.Def_PaddedDescent_F_ArithFits
import Definitions.Def_PaddedDescent_F_ArithTopInv
import Definitions.Def_PaddedDescent_F_ArithMark
import Definitions.Def_PaddedDescent_F_ArithA
import Theorems.Thm_PaddedDescent_F_Arith_stackLen_le
import Theorems.Thm_PaddedDescent_F_Arith_top_rounds
import Theorems.Thm_PaddedDescent_le_of_s0K_le
import Theorems.Thm_PaddedDescent_leafC_add_two_le


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Arith
namespace PaddedDescent.F
theorem _root_.solution : StAW := fun _k _n _F hk hs hF =>
  ⟨le_of_s0K_le hs, leafC_add_two_le hs, top_rounds hs hF, stackLen_le hk hs (by norm_num) hF⟩
end PaddedDescent.F
