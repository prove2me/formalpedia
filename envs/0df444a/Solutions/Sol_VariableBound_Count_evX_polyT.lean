-- Prove2me | solution 1 for VariableBound.Count.evX_polyT
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:01:25.312836+00:00
-- url     : https://prove2.me/submissions/7257946b-b199-473d-843b-4f3ace246abf

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Count_Defs
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_VariableBound_Count_Cert
import Theorems.Thm_VariableBound_Count_mod_two_pow_polyT
import Theorems.Thm_Groundwork_PB_const
import Theorems.Thm_Groundwork_PolyT_const
import Theorems.Thm_Groundwork_Unary_const
attribute [local fun_prop] Groundwork.PolyT.const



set_option autoImplicit false
section
section
open VariableBound VariableBound.Count
open Groundwork Groundwork.Prog PaddedDescent.F ClauseBound.Alg AppVariables VariableBound.Net
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] {S : Solver Idx}
namespace VariableBound.Count
theorem _root_.solution (hEv : Net.StCertEvD) (hP : S.Poly) {k n Δ nb M β : α → ℕ} {pad : α → U} {i : α → Idx} {D : α → Dat} (hk : Unary k) (hn : Unary n) (hΔ : Unary Δ)
    (hnb : PolyT nb) (hM : PolyT M) (hβ : Unary β) (hp : PolyT pad) (hi : PolyT i) (hD : PolyT D) :
    PolyT fun x => evX S (k x) (pad x) (i x) (n x) (Δ x) (nb x) (M x) (β x) (D x) := by
  unfold evX
  exact mod_two_pow_polyT (hEv Idx S hP α k n Δ nb M pad i (fun _ => false) D hk hn hΔ hnb hM hp hi (PolyT.const false) hD) hβ
end VariableBound.Count
