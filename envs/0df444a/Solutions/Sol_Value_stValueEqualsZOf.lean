-- Prove2me | solution 1 for Value.stValueEqualsZOf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:55:05.638772+00:00
-- url     : https://prove2.me/submissions/8ab915f0-64c6-435d-b224-edee533a87de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Clique
import Definitions.Def_Value_Joint
import Definitions.Def_Value_End

set_option autoImplicit false
section
section
open Value
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Eight.SecNetworks Eight.ViaGrouping
namespace Value
theorem _root_.solution : StValueEqualsZOf := by
  intro hC hJ hS C _ g K hK0 Np c N P B τ S h x L hL
  unfold groupClique
  rw [hC K L (display Np c N hK0 x), hJ C g K hK0 Np c N P B τ S h x L hL]
  exact sum_congr rfl fun z hz => hS g K P B N h.is (Paper.grouping hK0 x) z hz
end Value
