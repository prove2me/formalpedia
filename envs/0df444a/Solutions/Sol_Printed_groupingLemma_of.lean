-- Prove2me | solution 1 for Printed.groupingLemma_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:57:41.146419+00:00
-- url     : https://prove2.me/submissions/0024cc15-8cc6-4989-bc39-d14af56626cc

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingProcs
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_GroupingPoly
import Mathlib.Tactic
import Definitions.Def_Printed_Grouping
import Theorems.Thm_Printed_stGroupingPoly


set_option autoImplicit false
section
section
open Printed
open QueryMachines
namespace Printed
theorem _root_.solution (h : StGroupingTied) : GroupingLemma := fun K e ⟨hK, h0, M, Cc, hp, hM⟩ =>
  let ⟨C₁, hC⟩ := h K e M Cc hK h0 hM
  ⟨groupingMachine K (3 * K ^ 8) M, C₁, stGroupingPoly K _ M hp, hC⟩
end Printed
