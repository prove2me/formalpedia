-- Prove2me | solution 1 for P2M_PaddedDescent_F_Lists_len_list_le__7630c2814a7f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T15:39:07.597525+00:00
-- url     : https://prove2.me/submissions/c8be1790-6a77-4adc-9500-1b107e3262e2

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_LenList
import Theorems.Thm_PaddedDescent_F_Lists_len_list_le

set_option autoImplicit false
section
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Lists
open Groundwork
namespace PaddedDescent.F.Lists
theorem _root_.solution {α : Type} [Enc α] (w : List α) {k : ℕ} (c : ℕ) (hk : w.length ≤ k) (h : ∀ a ∈ w, len a + 2 ≤ c) :
    len w ≤ k * c + 2 :=
  (len_list_le w c h).trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 2)
end PaddedDescent.F.Lists
