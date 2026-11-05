-- Prove2me | solution 1 for PaddedDescent.eOf_enc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T20:35:47.583828+00:00
-- url     : https://prove2.me/submissions/6e873a06-97b5-40cf-a2e2-5adc9dfd67a3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_PadRate
import Definitions.Def_PaddedDescent_BrutePad
import Definitions.Def_ToTuring_Poly_Decode
import Definitions.Def_PaddedDescent_Reduce
import Theorems.Thm_PaddedDescent_nOf_enc


set_option autoImplicit false
section
open PaddedDescent
open Groundwork Groundwork.Decode Sat3 Turing
namespace PaddedDescent
theorem _root_.solution (C₀ : ℕ) {n : ℕ} {φ : CNF n} (h : Is3CNF φ) : eOf C₀ (enc φ) = padLog C₀ n := by
  rw [eOf, nOf_enc h]
end PaddedDescent
