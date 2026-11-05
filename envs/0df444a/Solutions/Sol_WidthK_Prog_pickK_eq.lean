-- Prove2me | solution 1 for WidthK.Prog.pickK_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T19:35:50.72259+00:00
-- url     : https://prove2.me/submissions/caf3ce03-036d-42e0-802e-ca33bddc65a5

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsifyWidthK_Interfaces
import Definitions.Def_SparsifyWidthK_Poly_Sparsify
import Theorems.Thm_Groundwork_PolyT_filterMap
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.filterMap
attribute [local fun_prop] Groundwork.PolyT.map



set_option autoImplicit false
section
section
open WidthK WidthK.Prog
open Groundwork Groundwork.Sparsify
variable {α : Type} [Enc α]
namespace WidthK.Prog
theorem _root_.solution (θ : ℕ → ℕ) (k : ℕ) (s : PFml) :
    pickK θ k s = (((pairsK k).map fun jh => (jh, θ (jh.1 - jh.2))).filterMap (tryT k s)).head? := by
  rw [List.filterMap_map]; rfl
end WidthK.Prog
