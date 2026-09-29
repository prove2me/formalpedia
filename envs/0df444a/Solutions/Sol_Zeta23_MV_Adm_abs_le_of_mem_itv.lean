-- Prove2me | solution 1 for Zeta23.MV.Adm.abs_le_of_mem_itv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T07:39:50.039333+00:00
-- url     : https://prove2.me/submissions/ba5c8482-778d-42ac-a19a-413a4d6b547e

import Mathlib
import Definitions.Def_Zeta23_MV_Spacing

-- from Zeta23.MV.Spacing
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/


/-!
# MV step 0 — spacing lemmas for admissible weights

For an injective `freq : ι → ℝ` on a finite index type with ADMISSIBLE weights `δ`
(`0 < δ r` and `δ r ≤ |freq r − freq s|` for all `s ≠ r` — the shape of Zeta23.MVHilbert),
the open intervals `I_t = (freq t − δ t/2, freq t + δ t/2)` are pairwise disjoint, giving
by comparison with `∫ |u − freq s|^{−σ} du`:

* `spacing_sq`   (σ = 2):  Σ_{t≠s} δ t/(freq s − freq t)²  ≤  9/δ s
* `spacing_four` (σ = 4):  Σ_{t≠s} δ t/(freq s − freq t)⁴  ≤  27/(δ s)³
* `two_point`:  Σ_{k≠ℓ,m} δ k/((freq k − freq ℓ)²(freq k − freq m)²)
                  ≤ 36(δ ℓ + δ m)/(δ ℓ · δ m · (freq ℓ − freq m)²)

These replace [Preissmann 1984, Lemmes 1 & 6] (cited without proof in arXiv:2203.14950)
with elementary arguments at worse constants — sufficient for the ∃C form.
-/

noncomputable section
open MeasureTheory Real Set Finset
open scoped BigOperators

namespace Zeta23
namespace MV

variable {ι : Type*} [Fintype ι] [DecidableEq ι]


namespace Adm

variable {freq δ : ι → ℝ} (h : Adm freq δ)








section MainSpacing
variable (h : Adm freq δ) (s : ι)





end MainSpacing





end Adm
end MV
end Zeta23
end
open MeasureTheory Real Set Finset
open scoped BigOperators
open Zeta23
open MV
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
open Adm
variable {freq δ : ι → ℝ} (h : Adm freq δ)
omit [Fintype ι] [DecidableEq ι]

theorem solution (h : Adm freq δ) {s t : ι} (hts : t ≠ s) {u : ℝ}
    (hu : u ∈ Adm.itv (freq := freq) (δ := δ) t) :
    |freq s - u| ≤ 3 / 2 * |freq s - freq t| ∧ δ s / 2 ≤ |u - freq s| := by
  simp only [Adm.itv, Set.mem_Ioo] at hu
  have hut : |u - freq t| ≤ δ t / 2 := by rw [abs_le]; constructor <;> linarith
  have hst : δ t ≤ |freq s - freq t| := by rw [abs_sub_comm]; exact h.le t s hts
  have hss : δ s ≤ |freq s - freq t| := h.le s t (Ne.symm hts)
  constructor
  · calc |freq s - u| = |(freq s - freq t) + (freq t - u)| := by ring_nf
      _ ≤ |freq s - freq t| + |freq t - u| := abs_add_le _ _
      _ = |freq s - freq t| + |u - freq t| := by rw [abs_sub_comm (freq t) u]
      _ ≤ |freq s - freq t| + δ t / 2 := by linarith
      _ ≤ 3 / 2 * |freq s - freq t| := by linarith
  · have key : |freq s - freq t| ≤ |freq s - u| + |u - freq t| := by
      calc |freq s - freq t| = |(freq s - u) + (u - freq t)| := by ring_nf
        _ ≤ |freq s - u| + |u - freq t| := abs_add_le _ _
    rw [abs_sub_comm u (freq s)]
    linarith
