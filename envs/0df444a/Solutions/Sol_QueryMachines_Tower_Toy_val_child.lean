-- Prove2me | solution 1 for QueryMachines.Tower.Toy.val_child
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:07:13.565297+00:00
-- url     : https://prove2.me/submissions/6b045cf4-4e84-4c33-99ef-5c0e746a0411

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Tower_Toy_Defs
import Definitions.Def_Tower_Toy_Spec
import Theorems.Thm_QueryMachines_Tower_Toy_sumF_congr

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Tower QueryMachines.Tower.Toy
open Groundwork
namespace QueryMachines.Tower.Toy
theorem _root_.solution (ℓ0 M0 l : ℕ) (b : Bool) (f : List Bool → Option ℕ) : (spec ℓ0 M0).val (l, b) ((spec ℓ0 M0).tab (l, b) f) = sumF l fun q => f (b :: q) :=
  sumF_congr l _ _ fun _ hq => if_pos hq
end QueryMachines.Tower.Toy
