-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.entry_eq_or_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:10:10.911758+00:00
-- url     : https://prove2.me/submissions/eaefbaf6-9e5c-4fbb-a51c-3999b43a6dcc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_QueryMachines_Bridge_Proof_getD_eq_or_mem

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
namespace QueryMachines.Bridge.Proof
theorem _root_.solution (T : Tab) (x : TableQuery) : entry T x = 0 ∨ ∃ r ∈ T, entry T x ∈ r := by
  unfold entry
  rcases getD_eq_or_mem T x.1 [] with h | h
  · left; rw [h]; rfl
  · rcases getD_eq_or_mem (T.getD x.1 []) (ofWord x.2) 0 with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨_, h, h'⟩
end QueryMachines.Bridge.Proof
