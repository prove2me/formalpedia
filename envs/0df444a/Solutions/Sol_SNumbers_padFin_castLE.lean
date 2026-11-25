-- Prove2me | solution 1 for SNumbers.padFin_castLE
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:40:58.555184+00:00
-- url     : https://prove2.me/submissions/7bbc7a64-131b-4dc9-a494-b6efa75e4813

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Theorems.Thm_SNumbers_padFin_apply
attribute [local simp] SNumbers.padFin_apply

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution (h : n ≤ m) (y : PiLp p (fun _ : Fin n => 𝕜)) (j : Fin n) :
    (padFin (p := p) (m := m) y) (Fin.castLE h j) = y j := by
  rw [padFin_apply, dif_pos (by simp only [Fin.val_castLE]; exact j.isLt)]
  congr 1
end SNumbers
