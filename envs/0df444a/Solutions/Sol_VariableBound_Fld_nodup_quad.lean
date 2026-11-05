-- Prove2me | solution 1 for VariableBound.Fld.nodup_quad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:15:58.60919+00:00
-- url     : https://prove2.me/submissions/36483896-fa74-4b27-ae6e-3e09e786d649

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
import Theorems.Thm_VariableBound_Fld_nodup_wordsL

set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset
namespace VariableBound.Fld
theorem _root_.solution (s : ℕ) : (wordsL s ×ˢ wordsL s ×ˢ wordsL s ×ˢ wordsL s).Nodup :=
  (nodup_wordsL s).product ((nodup_wordsL s).product ((nodup_wordsL s).product (nodup_wordsL s)))
end VariableBound.Fld
