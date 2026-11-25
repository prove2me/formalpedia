-- Prove2me | solution 1 for SNumbers.padFin_projFin_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:24:14.1598+00:00
-- url     : https://prove2.me/submissions/17940af2-22d1-413f-9e6b-d8ace6646344

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
theorem _root_.solution (h : n ≤ m) (x : PiLp p (fun _ : Fin m => 𝕜)) (i : Fin m) :
    (padFin (projFin (p := p) h x)) i = if (i : ℕ) < n then x i else 0 := by
  by_cases hi : (i : ℕ) < n
  · rw [padFin_apply, dif_pos hi, projFin_apply, if_pos hi]
    congr 1
  · rw [padFin_apply, dif_neg hi, if_neg hi]
end SNumbers
