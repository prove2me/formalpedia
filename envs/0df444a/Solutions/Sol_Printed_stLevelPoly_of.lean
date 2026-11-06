-- Prove2me | solution 1 for Printed.stLevelPoly_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:18:42.343923+00:00
-- url     : https://prove2.me/submissions/fdb4e3d1-3778-4cc5-9357-f79ca569c021

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Definitions.Def_ToTuring_Poly_GridSide
import Mathlib.Tactic
import Definitions.Def_Printed_LevelPoly
import Theorems.Thm_Printed_levelLoop_poly
import Theorems.Thm_Printed_levelDiv_poly

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (hG : StGroupingPoly) : StLevelPoly := by
  intro K g M hM
  obtain ⟨i1⟩ := levelLoop_poly g _ (hG K g M hM)
  obtain ⟨i2⟩ := levelDiv_poly g
  exact ⟨IsPolyQ.bind _ _⟩
end Printed
