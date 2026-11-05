-- Prove2me | solution 1 for SparsificationLemma.Cal.factIV
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:29:46.950798+00:00
-- url     : https://prove2.me/submissions/006a11aa-f71d-4475-8937-6190ac90abab

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_SparsificationLemma_Cal_Defs
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import Definitions.Def_SparsificationLemma_Cal_Beta
import Theorems.Thm_SparsificationLemma_Cal_stBetaLe
import Theorems.Thm_SparsificationLemma_Cal_geom_le

set_option autoImplicit false
section
section
open SparsificationLemma SparsificationLemma.Cal
open Finset
namespace SparsificationLemma.Cal
theorem _root_.solution : FactIV := by
  intro α k hα hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  rw [sum_Ico_eq_sum_range]
  refine le_trans (sum_le_sum fun i _ => ?_) (geom_le (q := 32 * α) (by omega) m)
  rw [Nat.add_comm 1 i]
  exact stBetaLe α i
end SparsificationLemma.Cal
