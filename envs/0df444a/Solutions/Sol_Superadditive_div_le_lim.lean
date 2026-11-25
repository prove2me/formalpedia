-- Prove2me | solution 1 for Superadditive.div_le_lim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:26:23.983249+00:00
-- url     : https://prove2.me/submissions/68c4870b-c0f6-473f-ac28-1ba9b849d2eb

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology
open Superadditive
variable {u : ℕ → ℝ} (h : Superadditive u)
namespace Superadditive
theorem _root_.solution (hbdd : BddAbove (range fun n ↦ u n / n)) {n : ℕ} (hn : n ≠ 0) :
    u n / n ≤ Superadditive.lim u := by
  rw [Superadditive.lim]
  exact le_csSup (hbdd.mono (image_subset_range _ _)) ⟨n, Nat.one_le_iff_ne_zero.2 hn, rfl⟩
end Superadditive
