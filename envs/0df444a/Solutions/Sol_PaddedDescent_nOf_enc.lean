-- Prove2me | solution 1 for PaddedDescent.nOf_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:04:45.297213+00:00
-- url     : https://prove2.me/submissions/1a4a7533-7c67-4d16-b6f6-58b5b8520cd6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_Pad
import Definitions.Def_StepMachines_Prog_Decode
import Definitions.Def_ToTuring_Poly_Decode
import Batteries.Data.Nat.Lemmas
import Definitions.Def_PaddedDescent_BrutePad
import Theorems.Thm_Groundwork_Decode_dec_enc


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing
namespace PaddedDescent
theorem _root_.solution {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : nOf (enc φ) = n := by
  rw [nOf, dec_enc h.1]
end PaddedDescent
