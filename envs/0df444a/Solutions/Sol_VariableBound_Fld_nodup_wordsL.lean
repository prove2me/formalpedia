-- Prove2me | solution 1 for VariableBound.Fld.nodup_wordsL
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-04T23:02:37.888066+00:00
-- url     : https://prove2.me/submissions/b9852c2a-3944-49bf-896b-5c497e42da3d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Defs
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Definitions.Def_VariableBound_Field_Transfer
import Theorems.Thm_Groundwork_toWord_injOn
set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset

theorem solution (s : ℕ) : (wordsL s).Nodup :=
  List.Nodup.map_on
    (fun x hx y hy h => toWord_injOn s (by simpa using hx) (by simpa using hy) h)
    List.nodup_range

end
end
