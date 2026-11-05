-- Prove2me | solution 1 for PaddedDescent.F.Mark.NSat.nSat_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:57:25.279713+00:00
-- url     : https://prove2.me/submissions/68fcbc7b-0aab-45db-bdd1-f90ea8a057a6

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_PaddedDescent_F_MarkMath
import Definitions.Def_StepMachines_Prog_Count
import Definitions.Def_PaddedDescent_F_NSat

set_option autoImplicit false
section
open PaddedDescent PaddedDescent.F PaddedDescent.F.Mark PaddedDescent.F.Mark.NSat
open Groundwork Groundwork.Prog
namespace PaddedDescent.F.Mark.NSat
theorem _root_.solution {n : ℕ} {x : Fml} (hx : ∀ C ∈ x, ∀ l ∈ C, l.1 < n) : 0 < nSat n x ↔ Fml.Sat x := by
  unfold nSat Fml.Sat
  rw [Finset.card_pos]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨ext σ, (Finset.mem_filter.1 hσ).2⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun i => a i.1, Finset.mem_filter.2 ⟨Finset.mem_univ _, fun C hC => ?_⟩⟩
    obtain ⟨l, hl, hal⟩ := ha C hC
    refine ⟨l, hl, ?_⟩
    rw [ext, dif_pos (hx C hC l hl)]
    exact hal
end PaddedDescent.F.Mark.NSat
