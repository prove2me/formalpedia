-- Prove2me | solution 1 for VariableBound.Net.CertNet.WD_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:36:38.621474+00:00
-- url     : https://prove2.me/submissions/98d763f6-8402-4842-8b4b-88f3fcefe0de

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.CertNet
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.ParityChecks.CertLib
open PaddedDescent.F.Mark (qv)
variable {α : Type} [Enc α]
namespace VariableBound.Net.CertNet
theorem _root_.solution (g n : ℕ) (D : Dat) (y : ℕ) (fl : Bool) (a : ℕ) (z : List Bool) : WD g n D y fl a z =
    if ok1 g n a z && ok2 g n D a z && ok3 g n D y a z && ok4 g n D y a z then sigP g n D a z * (bif fl then (-1) ^ sgE g n D a z else 1) else 0 := rfl
end VariableBound.Net.CertNet
