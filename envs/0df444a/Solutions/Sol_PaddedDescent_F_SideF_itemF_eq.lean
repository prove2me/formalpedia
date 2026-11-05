-- Prove2me | solution 1 for PaddedDescent.F.SideF.itemF_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:33:42.87776+00:00
-- url     : https://prove2.me/submissions/1fcd9d10-fab7-4bff-bea6-d9de6874a056

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_RebalG
import Definitions.Def_PaddedDescent_F_Price
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_NetworkStatements
import Mathlib.Algebra.Polynomial.Coeff
import Definitions.Def_PaddedDescent_F_SideF
import Theorems.Thm_PaddedDescent_F_SideF_cutF_eq
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_length_he_le
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.SideF
open Groundwork Groundwork.Prog Groundwork.Grid Finset
namespace PaddedDescent.F.SideF
theorem _root_.solution {pad : U} (g : ℕ) (tr : Bool) {n : ℕ} (y a b : ℕ) (z θ : List Bool) (i i' : ℕ)
    (h : 2 ^ n ≤ pad.length) : itemF pad g tr n y a b z θ i i' = sideItem g tr n y a b z θ i i' :=
  cutF_eq _ _ _ _ _ ((Nat.pow_le_pow_right (by norm_num) (length_he_le g n z i _)).trans h)
end PaddedDescent.F.SideF
