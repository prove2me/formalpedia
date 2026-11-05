-- Prove2me | solution 1 for SparsificationLemma.sat_rootP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:37:34.633477+00:00
-- url     : https://prove2.me/submissions/ff56f319-ca33-42fc-ae60-34d3c5742520

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Defs
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_CountKSat_StepCount
import Definitions.Def_SparsifyWidthK_ProgMain
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_SparsifyWidthK_Refine
import Definitions.Def_CountKSatRate_Leaf
import Definitions.Def_CountKSatRate_Leaf
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Tauto
import Definitions.Def_SparsificationLemma_One
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Sparsify_sat_red
import Theorems.Thm_Groundwork_TM_Run_trans
import Theorems.Thm_WidthK_ProgMain_sat_toFin
import Theorems.Thm_WidthK_Refine_toFin_rootP
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open SparsificationLemma
open Finset Groundwork Groundwork.Prog Groundwork.Sparsify WidthK WidthK.Prog CountKSat CountKSatRate
open CountKSat.StepCount
namespace SparsificationLemma
theorem _root_.solution (b : ℕ → Bool) (ψ : PFml) : Sat b (rootP ψ) ↔ Sat b ψ :=
  (ProgMain.sat_toFin (fun l : PLit => b l.1 = l.2) (rootP ψ)).symm.trans
    (Iff.trans (by rw [Refine.toFin_rootP, sat_red]) (ProgMain.sat_toFin (fun l : PLit => b l.1 = l.2) ψ))
end SparsificationLemma
