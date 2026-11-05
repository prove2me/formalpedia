-- Prove2me | solution 1 for P2M_ClauseBound_ParityChecks_CertPar_parQ___e24fc9b201b1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:28:07.70511+00:00
-- url     : https://prove2.me/submissions/fa417de9-f17d-4fb2-ac9e-156bf3ed2360

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
namespace ClauseBound.ParityChecks.CertPar
theorem _root_.solution (n Δ m : ℕ) : (parQ n Δ m).β = n + beta0 m (nbOf n Δ) + beta1 m (i0Of n) + 2 := by unfold parQ; split_ifs <;> rfl
end ClauseBound.ParityChecks.CertPar
