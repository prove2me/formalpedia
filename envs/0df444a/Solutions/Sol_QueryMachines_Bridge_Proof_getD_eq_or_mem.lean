-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.getD_eq_or_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:00:31.111333+00:00
-- url     : https://prove2.me/submissions/c54c2935-c135-479b-98fd-6b6930bde6c5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {γ : Type} (l : List γ) (i : ℕ) (d : γ) : l.getD i d = d ∨ l.getD i d ∈ l := by
  by_cases h : i < l.length
  · right; rw [List.getD_eq_getElem _ _ h]; exact List.getElem_mem h
  · left; exact List.getD_eq_default _ _ (not_lt.1 h)
end QueryMachines.Bridge.Proof
