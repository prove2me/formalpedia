-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.le_foldr_max
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:55:46.471583+00:00
-- url     : https://prove2.me/submissions/9e35954a-3cdc-4d4c-a92d-3745c7db1d69

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables
import Theorems.Thm_Groundwork_TM_Run_trans


set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 1 := by
  induction l with
  | nil => cases h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)
end QueryMachines.Bridge.Proof
