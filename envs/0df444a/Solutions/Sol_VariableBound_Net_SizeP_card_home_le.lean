-- Prove2me | solution 1 for VariableBound.Net.SizeP.card_home_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T06:42:46.997317+00:00
-- url     : https://prove2.me/submissions/cf34e584-6639-4f52-a392-453b9034df9d

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_VariableBound_Net_Tests
import Definitions.Def_VariableBound_Net_SizeB
import Definitions.Def_PaddedDescent_F_MarkDeg
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_VariableBound_Net_SizeP
import Theorems.Thm_VariableBound_Net_SizeP_le_qv_mul
import Theorems.Thm_Groundwork_PolyT_filter
attribute [local fun_prop] Groundwork.PolyT.filter



set_option autoImplicit false
section
section
open VariableBound VariableBound.Net VariableBound.Net.SizeP
open Groundwork Groundwork.Prog Finset
open PaddedDescent.F.Mark (Cl qv WfL occ)
variable {k g n Δ : ℕ} {D : Dat}
namespace VariableBound.Net.SizeP
theorem _root_.solution (hg : 0 < g) (r a : ℕ) : #((range r).filter fun j => home g j = a) ≤ qv g r := by
  rw [← card_range (qv g r)]
  refine card_le_card_of_injOn (fun j => j / g) ?_ ?_
  · intro j hj
    have h1 := mem_range.1 (mem_filter.1 (mem_coe.1 hj)).1
    exact mem_coe.2 (mem_range.2 ((Nat.div_lt_iff_lt_mul hg).2 (h1.trans_le (le_qv_mul hg r))))
  · intro j hj j' hj' heq
    have h1 : j % g = a := (mem_filter.1 (mem_coe.1 hj)).2
    have h2 : j' % g = a := (mem_filter.1 (mem_coe.1 hj')).2
    have h3 : j / g = j' / g := heq
    rw [← Nat.div_add_mod j g, ← Nat.div_add_mod j' g, h1, h2, h3]
end VariableBound.Net.SizeP
