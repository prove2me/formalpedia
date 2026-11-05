-- Prove2me | solution 1 for QueryMachines.Bridge.Proof.foldr_max_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T02:43:35.521869+00:00
-- url     : https://prove2.me/submissions/f5b5447d-fb67-42aa-be21-ec4ee71dd718

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedToPadded_Defs
import Definitions.Def_ToTuring_Poly_IsPoly
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertNet
import Definitions.Def_ToTuring_Poly_NetFun
import Definitions.Def_CountedToPadded_Tables

set_option autoImplicit false
section
section
open QueryMachines QueryMachines.Bridge QueryMachines.Bridge.Proof
open Groundwork Groundwork.Prog Groundwork.PolyT PaddedDescent.F ClauseBound.Alg Printed
namespace QueryMachines.Bridge.Proof
theorem _root_.solution {l : List ℕ} {c : ℕ} (hc : 1 ≤ c) (h : ∀ x ∈ l, x ≤ c) : l.foldr max 1 ≤ c := by
  induction l with
  | nil => exact hc
  | cons a l ih => exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))
end QueryMachines.Bridge.Proof
