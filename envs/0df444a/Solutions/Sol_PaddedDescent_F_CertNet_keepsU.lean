-- Prove2me | solution 1 for PaddedDescent.F.CertNet.keepsU
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T23:51:24.143984+00:00
-- url     : https://prove2.me/submissions/5cc8f30c-05b8-450c-8cf3-3e04c168e094

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.CertNet
open Groundwork Groundwork.Prog Groundwork.Prog.NetE PaddedDescent.F
variable {α β γ ε : Type} [Enc α] [Enc β] [Enc γ] [Enc ε]
variable {C : Type} [Enc C] {Np : PNet C}
namespace PaddedDescent.F.CertNet
theorem _root_.solution {F : FNet C} (hF : FKeeps F) : KeepsU F.toP := ⟨hF.n, hF.cap⟩
end PaddedDescent.F.CertNet
