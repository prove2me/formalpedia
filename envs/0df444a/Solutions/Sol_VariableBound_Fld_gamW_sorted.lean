-- Prove2me | solution 1 for VariableBound.Fld.gamW_sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:09:01.503136+00:00
-- url     : https://prove2.me/submissions/5e1843c4-7e97-432c-8010-bd19157b728e

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
theorem _root_.solution (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : (gamW m a g u).Pairwise (· < ·) :=
  List.Pairwise.sublist List.filter_sublist List.pairwise_lt_range
end VariableBound.Fld
