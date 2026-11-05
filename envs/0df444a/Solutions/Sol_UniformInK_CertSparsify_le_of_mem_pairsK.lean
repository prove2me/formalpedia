-- Prove2me | solution 1 for UniformInK.CertSparsify.le_of_mem_pairsK
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:44:53.368196+00:00
-- url     : https://prove2.me/submissions/91e15a77-94a5-4ee0-984e-8da1516c452f

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_UniformInK_Cert_Sparsify

set_option autoImplicit false
section
section
open UniformInK UniformInK.CertSparsify
open Groundwork Groundwork.Sparsify WidthK.Prog
variable {α : Type} [Enc α]
namespace UniformInK.CertSparsify
theorem _root_.solution {k : ℕ} {jh : ℕ × ℕ} (h : jh ∈ pairsK k) : jh.1 ≤ k := by
  unfold pairsK at h
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.1 h
  obtain ⟨_, _, rfl⟩ := List.mem_map.1 h
  have := List.mem_range.1 hj
  omega
end UniformInK.CertSparsify
