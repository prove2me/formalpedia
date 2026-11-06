-- Prove2me | solution 1 for Printed.levelDiv_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:27:03.169616+00:00
-- url     : https://prove2.me/submissions/02cf44a0-7caf-4072-8516-033fbe4104f8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_ToTuring_Poly_GridSide
import Mathlib.Tactic
import Definitions.Def_Printed_LevelPoly
import Theorems.Thm_Printed_lamOf_unary
import Theorems.Thm_Eight_Level_Cert_div_polyT
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (g : ℕ) :
    (QueryMachine.lift (Stepped.ofFun fun p : (List Unit × List Unit) × ℤ => p.2 / ((2 ^ (tOf p.1.1.length * nRect g) : ℕ) : ℤ)) : QueryMachine TableQuery ℤ ((List Unit × List Unit) × ℤ) ℤ).PolyTimeSteps := by
  have i5 := IsPolyT.ofFun (Eight.Level.Cert.div_polyT (lam := fun c : List Unit × List Unit => c.1.length) g lamOf_unary)
  exact ⟨IsPolyQ.lift _⟩
end Printed
