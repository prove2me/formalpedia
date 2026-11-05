-- Prove2me | solution 1 for PaddedDescent.F.Mark.NSat.cast_nSat_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:58:26.792395+00:00
-- url     : https://prove2.me/submissions/1d2f4dca-00df-4a11-bb7d-86e251d499c9

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkMath
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_PaddedDescent_F_NSat
import Theorems.Thm_PaddedDescent_F_Mark_NSat_nSat_pos_iff

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.NSat
open Groundwork Groundwork.Prog
namespace PaddedDescent.F.Mark.NSat
theorem _root_.solution {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) : 0 < (nSat n x : ℤ) ↔ Fml.Sat x := by
  rw [Int.natCast_pos]; exact nSat_pos_iff hx
end PaddedDescent.F.Mark.NSat
