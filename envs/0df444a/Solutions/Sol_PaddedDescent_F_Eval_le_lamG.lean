-- Prove2me | solution 1 for PaddedDescent.F.Eval.le_lamG
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:55:58.072725+00:00
-- url     : https://prove2.me/submissions/b33c829c-2498-45ad-ab0b-519a7a6dabe3

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_Interfaces
import Definitions.Def_PaddedDescent_F_LenList
import Definitions.Def_StepMachines_Prog_NetVal
import Definitions.Def_ToTuring_EncLemmas
import Definitions.Def_PaddedDescent_F_Eval

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Eval
open Groundwork Groundwork.Prog Groundwork.Prog.NetE
open PaddedDescent.F.Mark (Cl trunc Good nSat occ placeAt placeE layersE Asked MCtx markF markN adm nProf cls WfL)
namespace PaddedDescent.F.Eval
theorem _root_.solution {K g x Uv Pv Ub₀ P : ℕ} (hK : 0 < K) (h : K ^ 3 * x ≤ K ^ 3 + K * Uv + g * Pv) (hU : Uv ≤ Ub₀) (hP : Pv ≤ P) :
    x ≤ lamG K g Ub₀ P := by
  unfold lamG
  rw [Nat.le_div_iff_mul_le (Nat.pow_pos hK), Nat.mul_comm]
  have h1 : K * Uv ≤ K * Ub₀ := Nat.mul_le_mul_left _ hU
  have h2 : g * Pv ≤ g * P := Nat.mul_le_mul_left _ hP
  omega
end PaddedDescent.F.Eval
