-- Prove2me | solution 1 for PaddedDescent.F.certRebalG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:50:27.4588+00:00
-- url     : https://prove2.me/submissions/4e39b81c-3bc1-448b-8348-eb0eacdef575

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_PaddedDescent_Col_CertG
import Theorems.Thm_PaddedDescent_F_CertNet_rebalG_polyT

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F
theorem _root_.solution : StCertRebalG := fun _ _ _ hF _ _ _ _ _ _ _ hp hK hg hb hc => CertNet.rebalG_polyT hF hp hK hg hb hc
end PaddedDescent.F
