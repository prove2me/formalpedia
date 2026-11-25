-- Prove2me | solution 1 for SNumbers.L1Linf.sum_norm_le_sqrt_mul_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:25:41.437138+00:00
-- url     : https://prove2.me/submissions/7bdd2a96-f219-4b82-8410-30174306d74b

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
public import Theorems.Thm_SNumbers_sum_le_sqrt_card_mul_sqrt_sum_sq


set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open SNumbers SNumbers.L1Linf
variable {𝕜 : Type*} [RCLike 𝕜]
open scoped Finset
namespace SNumbers.L1Linf
theorem _root_.solution {m : ℕ} (v : EuclideanSpace 𝕜 (Fin m)) :
    ∑ i, ‖v i‖ ≤ Real.sqrt m * ‖v‖ := by
  refine (SNumbers.sum_le_sqrt_card_mul_sqrt_sum_sq fun i => ‖v i‖).trans ?_
  rw [EuclideanSpace.norm_eq, Fintype.card_fin]
end SNumbers.L1Linf
