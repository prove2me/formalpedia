-- Prove2me | solution 1 for SNumbers.padFin_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:34:25.250114+00:00
-- url     : https://prove2.me/submissions/bc8d1f2b-3f2c-4fa4-8dd6-025035597805

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution (y : PiLp p (fun _ : Fin n => 𝕜)) (i : Fin m) :
    (padFin (p := p) (m := m) y) i = if hi : (i : ℕ) < n then y ⟨i, hi⟩ else 0 := rfl
end SNumbers
