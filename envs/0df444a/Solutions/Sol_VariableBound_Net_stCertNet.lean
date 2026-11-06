-- Prove2me | solution 1 for VariableBound.Net.stCertNet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:37:23.878629+00:00
-- url     : https://prove2.me/submissions/b236f466-63c0-46e1-bf10-3571e7a63771

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Defs
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Net_CertNet
import Theorems.Thm_VariableBound_Net_CertNet_netD_keeps

set_option autoImplicit false
section
section
open VariableBound VariableBound.Net
namespace VariableBound.Net
theorem _root_.solution (h : StCertRank) : StCertNet := CertNet.netD_keeps h
end VariableBound.Net
