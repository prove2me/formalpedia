-- Prove2me | solution 1 for SNumbers.piLp_norm_le_card_rpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:13:55.272102+00:00
-- url     : https://prove2.me/submissions/b2ccf79a-732f-492f-9bf6-4c7166920479

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
public import Theorems.Thm_SNumbers_piLp_norm_restrict_le

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ}
namespace SNumbers
theorem _root_.solution {p q : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)]
    (hpq : p ≤ q) (hq : q ≠ ∞) (f : Fin m → 𝕜) :
    ‖(WithLp.toLp p f : PiLp p (fun _ : Fin m => 𝕜))‖
      ≤ (m : ℝ) ^ (1 / p.toReal - 1 / q.toReal) *
        ‖(WithLp.toLp q f : PiLp q (fun _ : Fin m => 𝕜))‖ := by
  have h := piLp_norm_restrict_le hpq hq Finset.univ f (fun i hi => absurd (Finset.mem_univ i) hi)
  rwa [Finset.card_univ, Fintype.card_fin] at h
end SNumbers
