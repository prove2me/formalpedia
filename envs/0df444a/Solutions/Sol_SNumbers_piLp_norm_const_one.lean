-- Prove2me | solution 1 for SNumbers.piLp_norm_const_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:15:11.460446+00:00
-- url     : https://prove2.me/submissions/bd3c425e-7b0e-45a4-ad07-a2a36a16d97f

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
public import Theorems.Thm_ContinuousLinearMap_rank_zero
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
public import Theorems.Thm_SNumbers_padFin_apply
public import Theorems.Thm_SNumbers_toReal_pos_of_ne_top
attribute [local simp] ContinuousLinearMap.rank_zero
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.padFin_apply



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
namespace SNumbers
theorem _root_.solution {p : ℝ≥0∞} [Fact (1 ≤ p)] (hp : p ≠ ∞) :
    ‖(WithLp.toLp p (fun _ : Fin m => (1 : 𝕜)))‖ = (m : ℝ) ^ (1 / p.toReal) := by
  have hP : 0 < p.toReal := toReal_pos_of_ne_top hp
  rw [PiLp.norm_eq_sum hP]
  have hsum : (∑ i : Fin m, ‖(WithLp.toLp p (fun _ : Fin m => (1 : 𝕜))) i‖ ^ p.toReal)
      = (m : ℝ) := by simp [Real.one_rpow]
  rw [hsum]
end SNumbers
