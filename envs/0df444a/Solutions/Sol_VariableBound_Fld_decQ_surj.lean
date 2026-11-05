-- Prove2me | solution 1 for VariableBound.Fld.decQ_surj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:33:07.216946+00:00
-- url     : https://prove2.me/submissions/981bc9d6-8495-42e4-9ef7-e80e5518d520

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Search
import Mathlib.Data.ZMod.Basic
import Definitions.Def_VariableBound_Field_Family
import Theorems.Thm_VariableBound_Fld_decW_surj
import Theorems.Thm_VariableBound_Fld_mem_quad


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Groundwork Finset Polynomial
attribute [local instance] fintypeFW
namespace VariableBound.Fld
theorem _root_.solution (g : List Bool) (w : FW g × FW g × FW g × FW g) :
    ∃ u ∈ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length ×ˢ wordsL g.length, decQ g u = w := by
  obtain ⟨w1, w2, w3, w4⟩ := w
  obtain ⟨u1, h1, rfl⟩ := decW_surj g w1
  obtain ⟨u2, h2, rfl⟩ := decW_surj g w2
  obtain ⟨u3, h3, rfl⟩ := decW_surj g w3
  obtain ⟨u4, h4, rfl⟩ := decW_surj g w4
  exact ⟨(u1, u2, u3, u4), mem_quad.2 ⟨h1, h2, h3, h4⟩, rfl⟩
end VariableBound.Fld
