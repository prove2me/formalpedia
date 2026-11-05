-- Prove2me | solution 1 for VariableBound.Fld.gamW_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:56:42.370011+00:00
-- url     : https://prove2.me/submissions/49000ba3-ffea-4f03-b878-d51b57165dbb

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
theorem _root_.solution (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : ∀ E ∈ gamW m a g u, E < m :=
  fun _ hE => List.mem_range.1 (List.mem_of_mem_filter hE)
end VariableBound.Fld
