-- Prove2me | solution 1 for UniformInK.CertSparsify.pickK_eq_pickL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:45:47.442265+00:00
-- url     : https://prove2.me/submissions/5e1425f1-f854-4abf-9426-56fa2944d742

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_UniformInK_Spars_Defs
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_UniformInK_Cert_Sparsify
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_WidthK_Prog_pickK_eq
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open UniformInK UniformInK.CertSparsify
open Groundwork Groundwork.Sparsify WidthK.Prog
variable {α : Type} [Enc α]
namespace UniformInK.CertSparsify
theorem _root_.solution (θ : ℕ → ℕ) (k : ℕ) (s : PFml) :
    pickK θ k s = pickL (masks k) ((pairsK k).map fun jh => (jh, θ (jh.1 - jh.2))) s := pickK_eq θ k s
end UniformInK.CertSparsify
