-- Prove2me | solution 1 for Paper.grouped_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:31:58.918202+00:00
-- url     : https://prove2.me/submissions/98cfca7a-d0f3-475b-8904-da95ba83c1d8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Paper_SecNetworks_Model
import Definitions.Def_StepMachines_Prog_BruteE
import Definitions.Def_StepMachines_Prog_NetProg
import Definitions.Def_StepMachines_Prog_NetRun
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Math_RebalanceArith
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_Poly_Spec
import Definitions.Def_ToTuring_Poly_Brute
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_ToTuring_Poly_Basic
import Definitions.Def_ToTuring_Poly_Range
import Definitions.Def_ToTuring_Poly_Comb
import Definitions.Def_Paper_SecNetworks_Networks
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_NetE_ZW_merged
import Theorems.Thm_Groundwork_Prog_NetE_lbLen_eq
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open Paper
open Groundwork Groundwork.Prog Finset
open NetE Stepped
variable {C : Type} {g K : ℕ}
namespace Paper
theorem _root_.solution (Np : NetworkProcedures C) {c : C} {N : Network (Fin g) (List Bool) (List Bool)} {P B τ S : ℕ}
    (hK0 : 0 < K) (hN : IsNetwork Np c N P B τ S) (x L : ℕ)
    (hL : ∀ γ γ' : Fin K, γ ≠ γ' → (N.merge (grouping hK0 x) [] []).c γ γ' ≤ L) :
    cliqueValue L (groupedTables Np c N hK0 x L) = N.value :=
  ZW_merged Np hK0 hN.presented x L fun G G' hlt => by
    rw [lbLen_eq Np hK0 hN.presented x hlt.ne]
    exact hL _ _ hlt.ne
end Paper
