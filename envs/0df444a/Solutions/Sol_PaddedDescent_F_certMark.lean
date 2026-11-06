-- Prove2me | solution 1 for PaddedDescent.F.certMark
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:54:32.389509+00:00
-- url     : https://prove2.me/submissions/fcffdcfa-5538-4bf6-b21e-175e31866e4f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_PaddedDescent_F_CertMark
import Theorems.Thm_PaddedDescent_F_Mark_Cert_markF_keeps

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F
open Groundwork Groundwork.Prog
namespace PaddedDescent.F
theorem _root_.solution : StCertMark := Mark.Cert.markF_keeps
end PaddedDescent.F
