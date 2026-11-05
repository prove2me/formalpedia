-- Prove2me | solution 1 for Value.existsUnique_pi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:40:35.987481+00:00
-- url     : https://prove2.me/submissions/6a0bfaf2-2f66-4975-9423-69bdfa4dafd1

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Value_Defs
import Definitions.Def_Value_Words
import Theorems.Thm_Groundwork_Stepped_Runs_unique


set_option autoImplicit false
section
section
open Value
open Groundwork Finset
namespace Value
theorem _root_.solution {ι X : Type*} (R : ι → X → Prop) (h : ∀ i, ∃! x, R i x) : ∃! f : ι → X, ∀ i, R i (f i) :=
  ⟨fun i => (h i).exists.choose, fun i => (h i).exists.choose_spec, fun _ hf' => funext fun i => (h i).unique (hf' i) (h i).exists.choose_spec⟩
end Value
