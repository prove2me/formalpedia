-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Capelli.whB_g_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:03:12.355288+00:00
-- url     : https://prove2.me/submissions/03ada563-c4b6-4961-b83c-33af3b9c88a8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_RowCol
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_CapelliWhittakerZero

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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
open ReciprocityTheory.ChartRestriction.DS
variable {M R : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup R] [Module ℂ R]
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
theorem _root_.solution {k r : ℕ} (ψ : Fin (k + 2 * r + 1) → Fin (k + 2 * r + 1) → ℂ) {a b0 : Fin (k + 2 * r + 1)}
    (h : IsSimplePair k r a b0) : whB_g k r ψ a = ψ a b0 := by
  unfold whB_g
  rw [Finset.prod_eq_single b0 (fun b _ hb => ?_) (by simp), if_pos h]
  rw [if_neg]
  intro hb'
  apply hb
  obtain ⟨h1, h2, h3⟩ := h
  obtain ⟨h1', h2', h3'⟩ := hb'
  simp only [inW, blk] at h1 h2 h3 h1' h2' h3'
  have := b.isLt; have := b0.isLt
  apply Fin.ext
  split_ifs at h1 h1' <;> omega
end ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
