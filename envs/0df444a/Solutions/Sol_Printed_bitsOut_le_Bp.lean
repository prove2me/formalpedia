-- Prove2me | solution 1 for Printed.bitsOut_le_Bp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T07:29:46.361723+00:00
-- url     : https://prove2.me/submissions/d05f1835-fdfe-4147-8373-d802b36e33bb

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_QueryMachines_CombRuns
import Definitions.Def_Eight_ViaGrouping_Main
import Mathlib.Tactic
import Definitions.Def_Printed_GroupingRun

set_option autoImplicit false
section
section
open Printed
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping QueryMachines QueryMachines.QueryMachine
namespace Printed
theorem _root_.solution {K : ℕ} (hK0 : 0 < K) (g P B : ℕ) : bitsOut K g P B ≤ Cost.Bp K g P B := by
  unfold bitsOut Cost.Bp
  refine Nat.add_le_add_right ?_ _
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈2 * ((g : ℝ) * P) / K⌉₊ := ⟨_, rfl⟩
  rw [← hn]
  have h1 : 2 * ((g : ℝ) * P) / K ≤ n := hn ▸ Nat.le_ceil _
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  rw [div_le_iff₀ hKr] at h1
  have h2 : 2 * (g * P) ≤ n * K := by exact_mod_cast h1
  exact Nat.lt_succ_iff.1 (Nat.div_lt_of_lt_mul (calc 2 * (g * P) + (K - 1) < n * K + K := by omega
    _ = K * (n + 1) := by ring))
end Printed
