-- Prove2me | solution 1 for VariableBound.Fld.stFamD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:03:01.281495+00:00
-- url     : https://prove2.me/submissions/00b91504-30d5-467a-a1ed-90bb9853567f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
import Theorems.Thm_VariableBound_Fld_fam_of
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_VariableBound_Fld_famD_eq
import Theorems.Thm_VariableBound_Fld_modW_spec
import Theorems.Thm_VariableBound_Fld_one_le_sD
import Theorems.Thm_VariableBound_Fld_sD_le
import Theorems.Thm_VariableBound_Fld_sD_lt


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset Polynomial
attribute [local instance] fintypeFW
namespace VariableBound.Fld
theorem _root_.solution (h14 : AppVariables.LemFamily) : StFamD := by
  intro m a ha hm
  have hm1 : 1 ≤ m := Nat.one_le_two_pow.trans hm
  obtain ⟨hlen, hirr⟩ := modW_spec (one_le_sD hm1)
  refine fam_of h14 m a (modW (sD m)) ha hm (by rw [hlen]; exact sD_le m) (by rw [hlen]; exact sD_lt hm1) hirr (famD m a) ?_
  rw [hlen]
  exact famD_eq m a
end VariableBound.Fld
