-- Prove2me | solution 1 for Printed.formula_isNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T08:25:36.735204+00:00
-- url     : https://prove2.me/submissions/e704620f-36d8-4691-8d22-656332be51c4

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_HandOver
import Definitions.Def_Eight_ViaGrouping_Count
import Mathlib.Tactic
import Definitions.Def_Printed_Count
import Theorems.Thm_Eight_ViaGrouping_satNet_isNetworkP
import Theorems.Thm_PaddedDescent_F_cap_eq


set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines
namespace Printed
theorem _root_.solution {g : ℕ} (hg : 0 < g) (k : ℕ) (Φ : Fml) :
    SecNetworks.IsNetwork (formulaProcs g k) Φ (satNet g k Φ) (satPf g k Φ) 1 1 (size Φ + 2 * g + 6 * (mu g Φ * k) + 8 + 2) :=
  have h := (satNet_isNetworkP hg k Φ).1
  ⟨h.is, h.τ_pos,
    { P_eq := h.given.P_eq, B_eq := rfl, len_eq := h.given.len_eq, cap_eq := h.given.cap_eq, mem_runs := h.given.mem_runs, W_runs := h.given.W_runs, Ψ_runs := h.given.Ψ_runs, f_runs := h.given.f_runs }⟩
end Printed
