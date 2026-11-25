-- Prove2me | solution 1 for Supermultiplicative.rpow_le_lim
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:28:03.88053+00:00
-- url     : https://prove2.me/submissions/e0365f45-3aed-4a2f-bb8e-f156cbee18b7

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
open Supermultiplicative
variable {u : ℕ → ℝ}
namespace Supermultiplicative
theorem _root_.solution (hbdd : BddAbove (range fun n ↦ u n ^ (n : ℝ)⁻¹)) {n : ℕ} (hn : n ≠ 0) :
    u n ^ (n : ℝ)⁻¹ ≤ Supermultiplicative.lim u := by
  rw [Supermultiplicative.lim]
  exact le_csSup (hbdd.mono (image_subset_range _ _)) ⟨n, Nat.one_le_iff_ne_zero.2 hn, rfl⟩
end Supermultiplicative
