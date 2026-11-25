-- Prove2me | solution 1 for Superadditive.tendsto_lim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:24.548146+00:00
-- url     : https://prove2.me/submissions/2c0cbd5e-5f6a-4e1b-8e0c-74e4d5b5ea5e

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
public import Theorems.Thm_Superadditive_subadditive_neg
public import Theorems.Thm_superadditive_neg_iff
public import Theorems.Thm_subadditive_neg_iff
public import Theorems.Thm_Superadditive_div_le_lim
attribute [local simp] superadditive_neg_iff
attribute [local simp] subadditive_neg_iff

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open Superadditive
variable {u : ℕ → ℝ} (h : Superadditive u)
include h
namespace Superadditive
theorem _root_.solution (hbdd : BddAbove (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop (𝓝 (Superadditive.lim u)) := by
  have hbdd' : BddBelow (range fun n ↦ -u n / n) := by
    obtain ⟨b, hb⟩ := hbdd
    exact ⟨-b, by rintro _ ⟨n, rfl⟩; simpa [neg_div] using hb ⟨n, rfl⟩⟩
  have hs := h.subadditive_neg
  have hneg : Tendsto (fun n ↦ u n / n) atTop (𝓝 (-hs.lim)) := by
    simpa [neg_div] using (hs.tendsto_lim hbdd').neg
  suffices -hs.lim = Superadditive.lim u by rwa [← this]
  refine le_antisymm (le_of_tendsto hneg ?_) ?_
  · filter_upwards [eventually_ne_atTop 0] with n hn
    exact div_le_lim hbdd hn
  · rw [Superadditive.lim]
    refine csSup_le ((nonempty_Ici).image _) fun _ ⟨n, hn, h'⟩ ↦ h' ▸ ?_
    have := hs.lim_le_div hbdd' (Nat.one_le_iff_ne_zero.1 hn)
    rw [neg_div] at this
    linarith
end Superadditive
