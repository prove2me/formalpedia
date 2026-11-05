-- Prove2me | solution 1 for PaddedDescent.F.RebalF.stRG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:36:58.325525+00:00
-- url     : https://prove2.me/submissions/fdfb11b9-39c1-4bf1-89d6-5046132df3fc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Col_Good
import Definitions.Def_PaddedDescent_F_RebalF
import Definitions.Def_PaddedDescent_F_RebalG
import Theorems.Thm_PaddedDescent_F_RebalF_rebalG_spec
import Theorems.Thm_PaddedDescent_F_RebalF_pos_of_colOK
import Theorems.Thm_PaddedDescent_Col_exists_goodG


set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.RebalF
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.Col Finset
namespace PaddedDescent.F.RebalF
theorem _root_.solution : StRG := by
  intro C pad K g β F c N P B M hK hcol hN hS hM0 hM hβ1 hβ f1 f2 f3 f4
  obtain ⟨m, h1, h2⟩ := id hcol
  exact rebalG_spec pad K g β F c N P B hK (pos_of_colOK (by omega) hcol) hβ1 hN hS
    (exists_goodG F.toP (by omega) hN hM0 (by unfold Dcol; exact Nat.one_le_two_pow) hM h1 h2 hβ) f1 f2 f3 f4
end PaddedDescent.F.RebalF
