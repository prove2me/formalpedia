-- Prove2me | solution 1 for Printed.tableQ_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:02:55.925221+00:00
-- url     : https://prove2.me/submissions/f829ffe6-ce8a-4cc4-83a0-d947d73fc9ec

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Definitions.Def_Eight_ViaGrouping_Keeps
import Definitions.Def_Exits_Poly
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingPoly
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Prog_NetE_isOne_polyT
import Theorems.Thm_Groundwork_Prog_NetE_isPsi_polyT
import Theorems.Thm_Groundwork_Prog_NetE_isW_polyT
import Theorems.Thm_Groundwork_Prog_NetE_nPairs_polyT
import Theorems.Thm_Groundwork_Prog_NetE_nStates_polyT
import Theorems.Thm_Groundwork_Prog_NetE_qF_polyT
import Theorems.Thm_Groundwork_Prog_NetE_qW_polyT
import Theorems.Thm_Groundwork_Prog_NetE_validB_polyT
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {Q A C : Type} [Enc Q] [Enc A] [HasSize C] [Enc C] [Carried C] (K g : ℕ) (Np : ProcsQ Q A C) (h : Np.under.toPaperNetwork.Keeps)
    [IsPolyQ Np.mem] [IsPolyQ Np.W] [IsPolyQ Np.Ψ] [IsPolyQ Np.f] : (tableQ K g Np).PolyTimeSteps := by
  have m1 := IsPolyQ.mapIn (qW_polyT K g h) Np.mem
  have m2 := IsPolyQ.mapIn (qW_polyT K g h) Np.W
  have m3 := IsPolyQ.mapIn (qMb_polyT K g h) Np.mem
  have m4 := IsPolyQ.mapIn (qPsi_polyT K g h) Np.Ψ
  have m5 := IsPolyQ.mapIn (qF_polyT K g h) Np.f
  have w : IsPolyQ (wQ K g Np) := IsPolyQ.gated _ _
  have p0 := IsPolyQ.gated (QueryMachine.mapIn (qMb K g Np.under) Np.mem) (QueryMachine.mapIn (qPsi K g Np.under) Np.Ψ)
  have p : IsPolyQ (psiQ K g Np) := IsPolyQ.gated _ _
  have f : IsPolyQ (fQ K g Np) := IsPolyQ.gated _ _
  have t1 := IsPolyQ.ite (isPsi_polyT K g) (psiQ K g Np) (fQ K g Np)
  have t2 := IsPolyQ.ite (isW_polyT g) (wQ K g Np) (QueryMachine.ite (isPsi K g) (psiQ K g Np) (fQ K g Np))
  have t3 : IsPolyQ (QueryMachine.const 1 : QueryMachine Q A ((X0 C × ℕ) × ℕ) ℤ) := IsPolyQ.const 1
  have t : IsPolyQ (termQ K g Np) := IsPolyQ.ite (isOne_polyT K g) _ _
  have s1 := IsPolyQ.prodRange (termQ K g Np) (nPairs_polyT g)
  have s2 := IsPolyQ.sumRange (QueryMachine.prodRange (nPairs g) (termQ K g Np)) (nStates_polyT K g h)
  have s3 : IsPolyQ (QueryMachine.const 0 : QueryMachine Q A (X0 C) ℤ) := IsPolyQ.const 0
  exact ⟨IsPolyQ.ite (validB_polyT K g h) _ _⟩
end Printed
