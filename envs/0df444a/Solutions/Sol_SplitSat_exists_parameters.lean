-- Prove2me | solution 1 for SplitSat.exists_parameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:22:04.29377+00:00
-- url     : https://prove2.me/submissions/6f5ea58c-1782-4b0a-9e1a-9669246747ab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SplitSat_Defs
import Definitions.Def_SplitSat_Cert
import Definitions.Def_SplitSat_Reader
import Definitions.Def_SplitSat_Procedure
import Definitions.Def_SplitSat_Simulate
import Definitions.Def_SparsificationLemma_TreeWalk_Walk
import Definitions.Def_ThreeSatPrinted_ThmEveryDelta
import Definitions.Def_WidthK_Top_EndLemmas
import Mathlib.Tactic
import Definitions.Def_SplitSat_Main
import Theorems.Thm_SplitSat_stSparsifyK
import Theorems.Thm_SplitSat_stReduce
import Theorems.Thm_SplitSat_stReduceCert


set_option autoImplicit false
section
section
open SplitSat
open Groundwork Groundwork.Prog Groundwork.Prog.SatTopK WidthK.Prog UniformInK Paper Eight.ViaGrouping
open scoped NNReal ENNReal
namespace SplitSat
theorem _root_.solution (k : ℕ) (hk : 3 ≤ k) (δ : ℝ) (hδ : 0 < δ) : ∃ (τ : ℕ) (δ₃ : ℝ), 0 < δ₃ ∧
    ∀ (D : StepMachine (List Unit × Fml) Bool) (c : ℕ), PolyTimeSteps D → Decides3 D δ₃ c →
      PolyTimeSteps (REDUCE k τ D) ∧ ∃ c' : ℕ, Decides (REDUCE k τ D) k δ c' := by
  obtain ⟨τ, Dd, B, Sk, hsp⟩ := stSparsifyK k hk (δ / 3) (by positivity)
  have hk3 : (0 : ℝ) ≤ (k : ℝ) - 3 := by
    have : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  have hpos : (0 : ℝ) < 1 + ((k : ℝ) - 3) * B := by
    have := mul_nonneg hk3 (Nat.cast_nonneg (α := ℝ) B)
    linarith
  have h0 : 0 < δ / 3 / (1 + ((k : ℝ) - 3) * B) := div_pos (by positivity) hpos
  exact ⟨τ, δ / 3 / (1 + ((k : ℝ) - 3) * B), h0, fun D c hp hD =>
    ⟨stReduceCert k τ D hp, stReduce k hk δ hδ τ Dd B Sk hsp D _ c h0.le (le_of_eq (div_mul_cancel₀ _ hpos.ne')) hD⟩⟩
end SplitSat
