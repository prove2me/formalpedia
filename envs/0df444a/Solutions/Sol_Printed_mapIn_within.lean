-- Prove2me | solution 1 for Printed.mapIn_within
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:20:58.160415+00:00
-- url     : https://prove2.me/submissions/70fe8725-29c9-4ea1-80ef-306e4d0be382

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun
import Theorems.Thm_QueryMachines_stMapInRuns


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {Q A α β γ : Type} {f : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {c : γ} (h : M.Within O w (f a) T S c) :
    (QueryMachine.mapIn f M).Within O w a T S c :=
  let ⟨own, L, hr, hle⟩ := h
  ⟨own, L, stMapInRuns _ _ _ _ _ f M O a own S L c hr, hle⟩
end Printed
