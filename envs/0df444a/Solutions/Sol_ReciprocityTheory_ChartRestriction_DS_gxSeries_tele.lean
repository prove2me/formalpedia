-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.gxSeries_tele
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:35.267211+00:00
-- url     : https://prove2.me/submissions/b047ffaa-245b-4c13-a8c4-de1d539591fa

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_GelfandSeries
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_gxSeries_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (l : Fin n → ℂ) (d : ℕ) : ∀ r : ℕ, n - r = d →
    1 - PowerSeries.X * ∑ s ∈ univ.filter (fun s : Fin n => r ≤ s.val), gxSeries l s =
      ∏ s ∈ univ.filter (fun s : Fin n => r ≤ s.val),
        (1 - PowerSeries.X * (1 - PowerSeries.C (l s) * PowerSeries.X)⁻¹) := by
  induction d with
  | zero =>
    intro r hr
    have : univ.filter (fun s : Fin n => r ≤ s.val) = ∅ := by
      ext s; simp; omega
    simp [this]
  | succ d ih =>
    intro r hr
    have hrn : r < n := by omega
    have hins : univ.filter (fun s : Fin n => r ≤ s.val) =
        insert ⟨r, hrn⟩ (univ.filter (fun s : Fin n => r + 1 ≤ s.val)) := by
      ext s; simp [Fin.ext_iff]; omega
    have hgt : univ.filter (fun s : Fin n => (⟨r, hrn⟩ : Fin n) < s) =
        univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by
      ext s; simp only [mem_filter, mem_univ, true_and, Fin.lt_def]; omega
    have hnot : (⟨r, hrn⟩ : Fin n) ∉ univ.filter (fun s : Fin n => r + 1 ≤ s.val) := by simp
    rw [hins, sum_insert hnot, prod_insert hnot, ← ih (r + 1) (by omega), gxSeries_eq l ⟨r, hrn⟩,
      hgt]
    ring
end ReciprocityTheory.ChartRestriction.DS
