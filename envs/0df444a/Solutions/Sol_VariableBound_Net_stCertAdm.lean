-- Prove2me | solution 1 for VariableBound.Net.stCertAdm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:48:42.243254+00:00
-- url     : https://prove2.me/submissions/e9ec646d-2ddd-4c9d-b747-ac8f68b23afd

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_VariableBound_Net_CertNet_admD_polyT

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
namespace VariableBound.Net
theorem _root_.solution : StCertAdm := fun _ _ _ _ _ _ _ _ _ _ hk hg hn hnb hM hD hfl hy => CertNet.admD_polyT hk hg hn hnb hM hD hfl hy
end VariableBound.Net
