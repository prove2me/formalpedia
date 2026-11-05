-- Prove2me | solution 1 for Wrap.Conf.size_drop_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T21:09:15.543124+00:00
-- url     : https://prove2.me/submissions/80778515-6b6c-46dc-a382-37826268abb0

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Wrap_Coding
import Definitions.Def_CircuitLowerBound_Tab_Sound
import Definitions.Def_ToTuring_Lib_Table
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Nat1
import Mathlib.Data.Finite.Sigma
import Mathlib.Tactic.Linarith
import Definitions.Def_Wrap_CodingExists
import Theorems.Thm_Wrap_Conf_size_append
import Theorems.Thm_Groundwork_size_list
attribute [local simp] Groundwork.size_list



set_option autoImplicit false
section
section
open Wrap Wrap.Conf
open Turing Groundwork CircuitLowerBound.Tab
namespace Wrap.Conf
theorem _root_.solution {α : Type} [HasSize α] (l : List α) (d : ℕ) : size (l.drop d) ≤ size l := by
  have h := size_append (l.take d) (l.drop d)
  rw [List.take_append_drop] at h
  have : 1 ≤ size (l.take d) := by rw [size_list]; omega
  omega
end Wrap.Conf
