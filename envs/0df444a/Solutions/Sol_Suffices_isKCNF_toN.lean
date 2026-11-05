-- Prove2me | solution 1 for Suffices.isKCNF_toN
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:29:45.687195+00:00
-- url     : https://prove2.me/submissions/b8819c27-272a-43bd-876d-7aac806f0ab6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Suffices_Sizes
import Definitions.Def_Exits_Runs
import Definitions.Def_CountKSat_InOut
import Definitions.Def_CountKSat_Poly
import Definitions.Def_Suffices_Loop
import Theorems.Thm_Groundwork_Decode_mem_toN
import Theorems.Thm_Groundwork_Decode_nil_mem_toN


set_option autoImplicit false
section
section
open Suffices
open Groundwork Groundwork.Prog Groundwork.Stepped CountKSat Paper SparsificationLemma Enumerate Exits
open Groundwork.Sparsify (leaves)
namespace Suffices
theorem _root_.solution {n : ℕ} {φ : Sat3.CNF n} (h3 : Sat3.Is3CNF φ) (hnil : [] ∉ φ) : IsKCNF 3 n (Decode.toN φ) := by
  intro D hD
  obtain ⟨⟨C, hC, hl⟩, h⟩ := Decode.mem_toN hD
  refine ⟨?_, hl ▸ h3.1 C hC, h⟩
  rintro rfl
  exact hnil ((Decode.nil_mem_toN φ).1 hD)
end Suffices
