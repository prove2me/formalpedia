-- Prove2me | solution 1 for Printed.answer_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T09:10:20.974469+00:00
-- url     : https://prove2.me/submissions/c9a8ccfb-f168-4e19-a02f-dc19b7cb9e73

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Programs
import Definitions.Def_QueryMachines_Poly
import Mathlib.Tactic
import Definitions.Def_Printed_HandOver
import Theorems.Thm_Printed_dist_polyT
import Theorems.Thm_Printed_bit_polyT
import Theorems.Thm_Groundwork_Sparsify_StackOK_mem


set_option autoImplicit false
section
section
open Printed
open Groundwork Groundwork.Prog Eight.SecNetworks QueryMachines
variable {Q A C : Type}
namespace Printed
theorem _root_.solution [Enc Q] [Enc A] [Enc C] (Np : ProcsQ Q A C) (hm : Np.mem.PolyTimeSteps) (hW : Np.W.PolyTimeSteps) (hΨ : Np.Ψ.PolyTimeSteps) (hf : Np.f.PolyTimeSteps) :
    Np.answer.PolyTimeSteps := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hW⟩ := hW
  obtain ⟨hΨ⟩ := hΨ
  obtain ⟨hf⟩ := hf
  have i1 := QueryMachine.IsPolyQ.mapOut Np.mem bit_polyT
  have i2 := QueryMachine.IsPolyQ.branch (sel := dist) Np.Ψ Np.f dist_polyT
  have i3 := QueryMachine.IsPolyQ.branch (sel := dist) Np.W (QueryMachine.branch dist Np.Ψ Np.f) dist_polyT
  exact ⟨QueryMachine.IsPolyQ.branch _ _ dist_polyT⟩
end Printed
