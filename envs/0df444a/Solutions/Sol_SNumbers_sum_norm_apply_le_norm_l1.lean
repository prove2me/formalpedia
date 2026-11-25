-- Prove2me | solution 1 for SNumbers.sum_norm_apply_le_norm_l1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:44:43.067814+00:00
-- url     : https://prove2.me/submissions/fd697f81-be50-4c8c-a375-65a3aed0ab35

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
variable {ι : Type*} [DecidableEq ι]
omit [DecidableEq ι]
namespace SNumbers
theorem _root_.solution (f : lp (fun _ : ι => 𝕜) 1) (J : Finset ι) :
    ∑ j ∈ J, ‖f j‖ ≤ ‖f‖ := by
  have h := lp.sum_rpow_le_norm_rpow (p := 1)
    (by norm_num : (0 : ℝ) < (1 : ℝ≥0∞).toReal) f J
  simpa using h
end SNumbers
