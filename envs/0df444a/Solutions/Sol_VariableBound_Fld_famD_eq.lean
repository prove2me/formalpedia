-- Prove2me | solution 1 for VariableBound.Fld.famD_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:21:54.651637+00:00
-- url     : https://prove2.me/submissions/608bf97c-4e85-4671-8a56-c099bf2a80c3

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

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset
namespace VariableBound.Fld
theorem _root_.solution (m a : ℕ) : famD m a =
    ((wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m) ×ˢ wordsL (sD m)).filter fun u =>
      decide (2 ^ a * (gamW m a (modW (sD m)) u).length ≤ 16 * m)).map (gamW m a (modW (sD m))) := by
  rw [famD, List.filter_map]; rfl
end VariableBound.Fld
