-- Prove2me | solution 1 for SNumbers.norm_idEmbed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:32:33.070909+00:00
-- url     : https://prove2.me/submissions/75c1cd9e-8a29-43f1-8069-0937b7b9d0d1

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
public import Theorems.Thm_SNumbers_piLp_norm_le_card_rpow_mul
public import Theorems.Thm_SNumbers_piLp_norm_const_one

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
namespace SNumbers
theorem _root_.solution [NeZero m] {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) :
    ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ = (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) := by
  have hpf : p ≠ ∞ := ne_top_of_le_ne_top hq hpq
  have hm : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  refine le_antisymm (opNorm_le_bound _ (by positivity) fun x => ?_) ?_
  · exact piLp_norm_le_card_rpow_mul hpq hq (WithLp.ofLp x)
  · have hb := (idEmbed (𝕜 := 𝕜) (m := m) p q).le_opNorm
      (WithLp.toLp q (fun _ : Fin m => (1 : 𝕜)))
    rw [show idEmbed (𝕜 := 𝕜) (m := m) p q (WithLp.toLp q (fun _ : Fin m => (1 : 𝕜)))
          = WithLp.toLp p (fun _ : Fin m => (1 : 𝕜)) from rfl,
      piLp_norm_const_one hpf, piLp_norm_const_one hq] at hb
    rw [Real.rpow_sub hm, div_le_iff₀ (by positivity)]
    exact hb
end SNumbers
