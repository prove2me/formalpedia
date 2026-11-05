-- Prove2me | solution 1 for VariableBound.Fld.gamW_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:56:41.232674+00:00
-- url     : https://prove2.me/submissions/fe120e82-5506-4ef3-aa05-88dcdd09f78a

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
theorem _root_.solution (m a : ℕ) (g : List Bool) (u : List Bool × List Bool × List Bool × List Bool) : (gamW m a g u).Nodup :=
  List.Nodup.sublist List.filter_sublist List.nodup_range
end VariableBound.Fld
