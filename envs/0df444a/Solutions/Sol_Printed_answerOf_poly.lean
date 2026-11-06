-- Prove2me | solution 1 for Printed.answerOf_poly
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:06:16.706218+00:00
-- url     : https://prove2.me/submissions/4bc99c60-7f9e-42bf-978b-aea37d3db478

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
theorem _root_.solution [Enc C] (Np : Procs C) (hm : Nonempty (IsPolyT Np.mem)) (hW : Nonempty (IsPolyT Np.W)) (hΨ : Nonempty (IsPolyT Np.Ψ)) (hf : Nonempty (IsPolyT Np.f)) :
    Nonempty (IsPolyT (answerOf Np)) := by
  obtain ⟨hm⟩ := hm
  obtain ⟨hW⟩ := hW
  obtain ⟨hΨ⟩ := hΨ
  obtain ⟨hf⟩ := hf
  have i1 : IsPolyT (Stepped.mapOut Np.mem fun b => if b = true then (1 : ℤ) else 0) := IsPolyT.mapOut bit_polyT
  have i2 : IsPolyT (Stepped.branch dist Np.Ψ Np.f) := IsPolyT.branch dist_polyT
  have i3 : IsPolyT (Stepped.branch dist Np.W (Stepped.branch dist Np.Ψ Np.f)) := IsPolyT.branch dist_polyT
  exact ⟨IsPolyT.branch dist_polyT⟩
end Printed
