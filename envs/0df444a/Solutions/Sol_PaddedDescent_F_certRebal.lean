-- Prove2me | solution 1 for PaddedDescent.F.certRebal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:44:52.517799+00:00
-- url     : https://prove2.me/submissions/b32835d3-715a-4caf-a2d3-a2d72f387702

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Theorems.Thm_PaddedDescent_F_CertNet_rebalF_polyT

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork
namespace PaddedDescent.F
theorem _root_.solution : StCertRebal := fun _ _ _ hF _ _ _ _ _ _ hp hK hg hc => CertNet.rebalF_polyT hF hp hK hg hc
end PaddedDescent.F
