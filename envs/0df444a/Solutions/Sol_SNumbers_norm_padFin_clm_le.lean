-- Prove2me | solution 1 for SNumbers.norm_padFin_clm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:10:07.724887+00:00
-- url     : https://prove2.me/submissions/d7baeac6-db60-4908-ac35-ba35ba74ddb4

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Theorems.Thm_SNumbers_norm_padFin_le

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution (h : n ≤ m) :
    ‖(padFin (𝕜 := 𝕜) (p := p) (n := n) (m := m))‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun y => by
    rw [one_mul]; exact norm_padFin_le h y
end SNumbers
