-- Prove2me | solution 1 for P2M_Groundwork_SatNet_mul_add_inj__c1cceb82cc73
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T16:08:14.535562+00:00
-- url     : https://prove2.me/submissions/ee66dc77-9d9f-4b8d-b8e6-238a17f85af8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ThreeSatStatement
import Definitions.Def_Groundwork_Net_Defs
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Definitions.Def_StepMachines_Math_SatNet
import Theorems.Thm_Groundwork_SatNet_mul_add_inj

set_option autoImplicit false
section
open Groundwork Groundwork.SatNet
open Finset
variable {V : Type}
namespace Groundwork.SatNet
theorem _root_.solution {k x y j j' : ℕ} (hj : j < k) (hj' : j' < k) (h : x * k + j = y * k + j') :
    x = y ∧ j = j' := mul_add_inj hj hj' h
end Groundwork.SatNet
