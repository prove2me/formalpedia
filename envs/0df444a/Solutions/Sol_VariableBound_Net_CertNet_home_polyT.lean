-- Prove2me | solution 1 for VariableBound.Net.CertNet.home_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:09:16.696884+00:00
-- url     : https://prove2.me/submissions/9c5cf1fd-9710-4be6-b6c6-26b3c16e6e7f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_Groundwork_PolyT_mod
attribute [local fun_prop] Groundwork.PolyT.mod



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]
namespace VariableBound.Net.CertNet
theorem _root_.solution {g j : α → ℕ} (hg : PolyT g) (hj : PolyT j) : PolyT fun x => home (g x) (j x) := by
  unfold home; exact PolyT.mod hj hg
end VariableBound.Net.CertNet
