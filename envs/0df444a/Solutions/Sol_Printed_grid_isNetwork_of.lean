-- Prove2me | solution 1 for Printed.grid_isNetwork_of
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T10:23:16.580053+00:00
-- url     : https://prove2.me/submissions/e6c76807-e771-4cd3-a2f9-4521324c27a8

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_CodingDefs
import Definitions.Def_Printed_Achievable
import Definitions.Def_Printed_GroupingProcs
import Definitions.Def_Eight_ViaGrouping_LevelEnd
import Mathlib.Tactic
import Definitions.Def_Printed_LevelNetworks
import Theorems.Thm_Eight_ViaGrouping_levelNetP_isNetworkP
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_PaddedDescent_F_cap_eq
import Theorems.Thm_Printed_gridProcs_close
attribute [local fun_prop] Groundwork.PolyT.length



set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution (hA : StAskServes) (g : ℕ) (hg : 1 ≤ g) : ∃ a : ℕ, ∀ (tr : Bool) (c : List Unit × List Unit) (lam B : ℕ) (W : ℕ → List Bool → ℤ) (y : ℕ), c.1.length = lam → c.2.length = B → 1 ≤ lam →
    (∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) → y < (tOf lam + 1) ^ nRect g →
    SecNetworks.IsNetwork ((gridProcs g tr).close (tables (g * g) lam W)) (c, y) (levelNetP g tr lam y (listTables (g * g) W)) (g ^ 3 * lam) (g * B + g ^ 2 * lam + 1) (a * (B + lam) ^ a)
      (size c + size (g * g) + g * g * (2 * lam + 2) + B + 3 + a * (size c + B + lam) ^ a + 2) := by
  obtain ⟨a, ha⟩ := levelNetP_isNetworkP g hg
  refine ⟨a, fun tr c lam B W y hcl hcB hl hW hy => ?_⟩
  subst hcl hcB
  have h := ha tr (List Unit × List Unit) (fun c => c.1.length) (askTable.close (tables (g * g) c.1.length W)) c c.2.length 1 _ (listTables (g * g) W) y hl le_rfl hy
    (hA (List Unit × List Unit) (g * g) c.1.length c.2.length W c hW)
  rw [Nat.mul_one] at h
  rw [gridProcs_close]
  exact ⟨h.is, h.τ_pos, { P_eq := h.given.P_eq, B_eq := rfl, len_eq := h.given.len_eq, cap_eq := h.given.cap_eq, mem_runs := h.given.mem_runs, W_runs := h.given.W_runs, Ψ_runs := h.given.Ψ_runs, f_runs := h.given.f_runs }⟩
end Printed
