-- Prove2me | solution 1 for Superadditive.tendsto_div_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:33.422355+00:00
-- url     : https://prove2.me/submissions/5bf40ee1-c574-4133-be82-bb55f0f71c50

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
public import Theorems.Thm_Subadditive_tendsto_div_atBot
public import Theorems.Thm_Superadditive_subadditive_neg
public import Theorems.Thm_superadditive_neg_iff
public import Theorems.Thm_subadditive_neg_iff
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
theorem _root_.solution (hbdd : ¬ BddAbove (range fun n ↦ u n / n)) :
    Tendsto (fun n ↦ u n / n) atTop atTop := by
  have hbdd' : ¬ BddBelow (range fun n ↦ -u n / n) := by
    rintro ⟨b, hb⟩
    exact hbdd ⟨-b, by rintro _ ⟨n, rfl⟩; have := hb ⟨n, rfl⟩; simp [neg_div] at this; linarith⟩
  have := tendsto_neg_atBot_atTop.comp (h.subadditive_neg.tendsto_div_atBot hbdd')
  simpa [neg_div, Function.comp_def] using this
end Superadditive
