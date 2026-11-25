-- Prove2me | solution 1 for SNumbers.L1Linf.norm_emb1_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:26:51.839376+00:00
-- url     : https://prove2.me/submissions/825f0ee5-b0de-465c-b7a0-634fdec01ac2

module
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_MaxDifference
public import Definitions.Def_BasicResults_LittleGrothendieck
public import Definitions.Def_BasicResults_SVD
public import Definitions.Def_AddOns_Approximable
public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Topology.MetricSpace.Sequences
public import Definitions.Def_SNumbers_Examples_IdentityL1Linfty
public import Theorems.Thm_SNumbers_L1Linf_sum_norm_le_sqrt_mul_norm
public import Theorems.Thm_SNumbers_L1Linf_emb1_apply

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
namespace SNumbers.L1Linf
theorem _root_.solution (m : ℕ) (v : EuclideanSpace 𝕜 (Fin m)) :
    ‖emb1 m v‖ ≤ Real.sqrt m * ‖v‖ := by
  have key : ‖(∑ i : Fin m, lp.single 1 (i : ℕ) (v i) : L1 𝕜)‖ ≤ Real.sqrt m * ‖v‖ := by
    refine (norm_sum_le _ _).trans ?_
    have hsum : ∑ i : Fin m, ‖(lp.single 1 (i : ℕ) (v i) : L1 𝕜)‖ = ∑ i : Fin m, ‖v i‖ :=
      Finset.sum_congr rfl fun i _ =>
        lp.norm_single (E := fun _ : ℕ => 𝕜) (show (0 : ℝ≥0∞) < 1 by norm_num) (i : ℕ) (v i)
    rw [hsum]
    exact sum_norm_le_sqrt_mul_norm v
  exact (congrArg Norm.norm (emb1_apply m v)).trans_le key
end SNumbers.L1Linf
