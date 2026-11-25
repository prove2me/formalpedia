-- Prove2me | solution 1 for SNumbers.L2Linf.sqrt_le_norm_toLp_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:18:04.909488+00:00
-- url     : https://prove2.me/submissions/931ef2ea-3d82-41ca-aba1-935c21cccc5d

module
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Operator.Prod
public import Definitions.Def_SNumbers_Examples_IdentityL2Linfty

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal ComplexConjugate
open ContinuousLinearMap
open SNumbers SNumbers.L2Linf
variable {𝕜 : Type u} [RCLike 𝕜]
namespace SNumbers.L2Linf
theorem _root_.solution {N k : ℕ} (w : Fin N → 𝕜)
    (hk : k ≤ (Finset.univ.filter fun i => ‖w i‖ = 1).card) :
    Real.sqrt k ≤ ‖(WithLp.toLp 2 w : PiLp 2 (fun _ : Fin N => 𝕜))‖ := by
  rw [PiLp.norm_eq_of_L2]
  refine Real.sqrt_le_sqrt ?_
  calc (k : ℝ)
      ≤ (Finset.univ.filter fun i => ‖w i‖ = 1).card := by exact_mod_cast hk
    _ = ∑ i ∈ Finset.univ.filter (fun i => ‖w i‖ = 1), ‖w i‖ ^ 2 := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.mem_filter.mp hi).2, one_pow, Nat.cast_one]
    _ ≤ ∑ i, ‖w i‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun i _ _ => sq_nonneg _
end SNumbers.L2Linf
