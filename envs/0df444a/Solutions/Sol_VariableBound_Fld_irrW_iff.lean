-- Prove2me | solution 1 for VariableBound.Fld.irrW_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:32:03.987136+00:00
-- url     : https://prove2.me/submissions/a7d67d1a-f517-4040-a745-e55ce607e619

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Field_Ring
import Definitions.Def_VariableBound_Field_Quot
import Definitions.Def_VariableBound_Field_Transfer
import Definitions.Def_VariableBound_Field_Search
import Theorems.Thm_VariableBound_Fld_decW_zeroW
import Theorems.Thm_VariableBound_Fld_decW_oneW
import Theorems.Thm_VariableBound_Fld_decW_mulW
import Theorems.Thm_VariableBound_Fld_irrW_eq_true
import Theorems.Thm_VariableBound_Fld_decW_inj
import Theorems.Thm_VariableBound_Fld_decW_surj
import Theorems.Thm_VariableBound_Fld_irreducible_of_inv
import Theorems.Thm_VariableBound_Fld_length_mulW
import Theorems.Thm_VariableBound_Fld_length_oneW
import Theorems.Thm_VariableBound_Fld_length_zeroW


set_option autoImplicit false
section
section
open VariableBound VariableBound.Fld
open Polynomial
namespace VariableBound.Fld
theorem _root_.solution {g : List Bool} (hg : 1 ≤ g.length) : irrW g = true ↔ Irreducible (modP g) := by
  rw [irrW_eq_true]
  constructor
  · intro h
    refine irreducible_of_inv g hg fun z hz => ?_
    obtain ⟨x, hx, rfl⟩ := decW_surj g z
    rcases h x hx with rfl | ⟨y, _, hy⟩
    · exact absurd (decW_zeroW g) hz
    · exact ⟨decW g y, by rw [← decW_mulW g hx, hy, decW_oneW]⟩
  · intro h x hx
    have : Fact (Irreducible (modP g)) := ⟨h⟩
    by_cases h0 : x = zeroW g
    · exact Or.inl h0
    · right
      have hne : decW g x ≠ 0 := fun e => h0 (decW_inj g hx (length_zeroW g) (by rw [e, decW_zeroW]))
      obtain ⟨y, hy, hyz⟩ := decW_surj g (decW g x)⁻¹
      refine ⟨y, hy, decW_inj g (length_mulW hx y) (length_oneW hg) ?_⟩
      rw [decW_mulW g hx, hyz, decW_oneW, mul_inv_cancel₀ hne]
end VariableBound.Fld
