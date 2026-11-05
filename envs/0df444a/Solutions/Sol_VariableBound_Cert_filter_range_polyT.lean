-- Prove2me | solution 1 for VariableBound.Cert.filter_range_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T00:52:11.657864+00:00
-- url     : https://prove2.me/submissions/fdeb9a2b-caa4-4fbe-be8e-b9aff599ec43

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Params_Defs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_VariableBound_Params_Cert
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open VariableBound
open Groundwork AppVariables PaddedDescent.F ClauseBound.ParityChecks.CertLib
open VariableBound.Cert
variable {α : Type} [Enc α]
namespace VariableBound.Cert
theorem _root_.solution {n : α → ℕ} {f : α → ℕ → Bool} (hn : Unary n) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (n p.1))) :
    PolyT fun x => (List.range (n x)).filter (f x) :=
  (PolyT.filter (f := fun x k => f x (min k (n x))) hf (PolyT.range hn)).congr fun x =>
    List.filter_congr fun k hk => by rw [min_eq_left (List.mem_range.1 hk).le]
end VariableBound.Cert
