-- Prove2me | solution 1 for VariableBound.Fld.length_gamW
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:48:19.671687+00:00
-- url     : https://prove2.me/submissions/20400a28-765f-4f75-b02f-5fbfc79268c8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
import Theorems.Thm_VariableBound_Fld_setD_gamW
import Theorems.Thm_VariableBound_Fld_card_setD
import Theorems.Thm_VariableBound_Fld_gamW_lt
import Theorems.Thm_VariableBound_Fld_gamW_nodup


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset Polynomial
attribute [local instance] fintypeFW
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) [Fact (Irreducible (modP g))] (hg : 1 ≤ g.length) (m a : ℕ) (hm : m ≤ 2 ^ g.length)
    {u : List Bool × List Bool × List Bool × List Bool} (hu : u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length) :
    (gamW m a g u).length = #(AppVariables.Gam (bitsW g) (thetaW g m hm) a (decQ g u)) := by
  rw [← setD_gamW g hg m a hm hu, card_setD (gamW_nodup m a g u) (gamW_lt m a g u)]
end VariableBound.Fld
