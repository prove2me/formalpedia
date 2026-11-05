-- Prove2me | solution 1 for VariableBound.Fld.decW_powW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:30:31.866728+00:00
-- url     : https://prove2.me/submissions/68fb2875-7229-430f-8e45-d9da03a5baee

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
import Theorems.Thm_VariableBound_Fld_decR_powW
import Theorems.Thm_VariableBound_Fld_root_pow
import Theorems.Thm_VariableBound_Fld_two_eq_zero_FW


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
namespace VariableBound.Fld
theorem _root_.solution {g : List Bool} (hg : 1 ≤ g.length) (u : List Bool) (e : ℕ) : decW g (powW g u e) = decW g u ^ e :=
  decR_powW (two_eq_zero_FW g) (root_pow g) hg u e
end VariableBound.Fld
