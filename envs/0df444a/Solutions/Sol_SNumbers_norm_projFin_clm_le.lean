-- Prove2me | solution 1 for SNumbers.norm_projFin_clm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:01.966218+00:00
-- url     : https://prove2.me/submissions/c28af824-9488-4ece-ac90-e6d7b93a7d2c

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Theorems.Thm_SNumbers_norm_projFin_le

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution (h : n ≤ m) : ‖projFin (𝕜 := 𝕜) (p := p) h‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact norm_projFin_le h x
end SNumbers
