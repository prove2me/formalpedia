-- Prove2me | solution 1 for PaddedDescent.F.stCertSide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:18.00798+00:00
-- url     : https://prove2.me/submissions/b5764804-720b-4521-909c-6e86e3b5eff2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_GridSide
import Definitions.Def_PaddedDescent_F_CertSide
import Theorems.Thm_PaddedDescent_F_CertSide_side_n
import Theorems.Thm_PaddedDescent_F_CertSide_side_cap
import Theorems.Thm_PaddedDescent_F_CertSide_side_W
import Theorems.Thm_PaddedDescent_F_CertSide_side_f

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F
namespace PaddedDescent.F
theorem _root_.solution : StCertSide := ⟨CertSide.side_n, CertSide.side_cap, CertSide.side_W, CertSide.side_f⟩
end PaddedDescent.F
