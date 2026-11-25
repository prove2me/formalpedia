-- Prove2me | solution 1 for SNumbers.norm_sq_eq_tsum_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:46:18.065328+00:00
-- url     : https://prove2.me/submissions/5772c210-3f82-4f13-8795-71e98a2d1ed0

module
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Theorems.Thm_SNumbers_signedSum_empty
attribute [local simp] SNumbers.signedSum_empty

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers
variable {𝕜 : Type*} [RCLike 𝕜]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
namespace SNumbers
theorem _root_.solution {ι : Type*} {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    (f : lp E 2) : ‖f‖ ^ 2 = ∑' i, ‖f i‖ ^ 2 := by
  have h := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) f
  rw [show ((2 : ℝ≥0∞)).toReal = (2 : ℝ) by norm_num] at h
  simpa using h
end SNumbers
