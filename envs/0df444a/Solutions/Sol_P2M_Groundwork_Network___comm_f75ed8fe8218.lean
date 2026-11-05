-- Prove2me | solution 1 for P2M_Groundwork_Network___comm_f75ed8fe8218
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:54:43.622723+00:00
-- url     : https://prove2.me/submissions/64802486-7eeb-4957-97b2-16d7f25a048a

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Net_Defs
import Definitions.Def_Groundwork_Net_Calculus
import Definitions.Def_Groundwork_Net_Net
import Theorems.Thm_Groundwork_Network_lab_comm

set_option autoImplicit false
section
open Groundwork
open Finset
variable {J J' σ τ A A' : Type*}
open Groundwork.Network
namespace Groundwork.Network
theorem _root_.solution [LinearOrder J] (N : Network J σ τ) (a b : J) (z z' : σ) : N.Ψ a b z z' = N.Ψ b a z' z := by
  unfold Ψ
  rw [lab_comm]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
end Groundwork.Network
