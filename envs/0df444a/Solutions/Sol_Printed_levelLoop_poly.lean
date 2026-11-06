-- Prove2me | solution 1 for Printed.levelLoop_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:07:33.313229+00:00
-- url     : https://prove2.me/submissions/b612a1b1-6d43-48b9-b935-e55bf70b0820

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_ToTuring_Poly_GridSide
import Mathlib.Tactic
import Definitions.Def_Printed_LevelPoly
import Theorems.Thm_Printed_lamOf_unary
import Theorems.Thm_Printed_networkOn_gridProcs_poly
import Theorems.Thm_Eight_Level_Cert_numPat8_polyT
import Theorems.Thm_Eight_Level_Cert_useRowP_polyT
import Theorems.Thm_Eight_stKeeps
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (g : ℕ) (NM : NetMachine) (hN : NM.PolyTimeSteps) :
    (QueryMachine.sumRange (numPat8 g fun c : List Unit × List Unit => c.1.length)
      (QueryMachine.ite (useRowP g fun c : List Unit × List Unit => c.1.length) (networkOn g NM (gridProcs g false)) (networkOn g NM (gridProcs g true)))).PolyTimeSteps := by
  have hl := lamOf_unary
  obtain ⟨i1⟩ := networkOn_gridProcs_poly g false NM hN
  obtain ⟨i2⟩ := networkOn_gridProcs_poly g true NM hN
  have i3 := IsPolyQ.ite (Eight.Level.Cert.useRowP_polyT (lam := fun c : List Unit × List Unit => c.1.length) Eight.stKeeps g hl) (networkOn g NM (gridProcs g false)) (networkOn g NM (gridProcs g true))
  exact ⟨IsPolyQ.sumRange _ (Eight.Level.Cert.numPat8_polyT (lam := fun c : List Unit × List Unit => c.1.length) g hl)⟩
end Printed
