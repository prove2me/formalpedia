-- Prove2me | solution 1 for SNumbers.norm_DiagCLMpq_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:23:08.3172+00:00
-- url     : https://prove2.me/submissions/7ced9656-4fda-4dc4-8407-e867ccfdbeef

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Bernstein
public import Definitions.Def_SNumbers_Gelfand
public import Definitions.Def_SNumbers_Kolmogorov
public import Definitions.Def_SNumbers_Hilbert
public import Definitions.Def_SNumbers_PiLpCoordinates
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Definitions.Def_SNumbers_Examples_Identity
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_DiagonalMatrices
public import Theorems.Thm_SNumbers_approximationNumber_zero_eq_norm
attribute [local simp] SNumbers.approximationNumber_zero_eq_norm



set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
variable {q : ℝ≥0∞} [Fact (1 ≤ q)]
namespace SNumbers
theorem _root_.solution [NeZero m] (hpq : p < q) (hq : q ≠ ∞) (σ : Fin m → 𝕜)
    (hσ : _root_.Antitone fun i => ‖σ i‖) :
    ‖DiagCLMpq p q σ‖ = (∑ i, ‖σ i‖ ^ diagExp p q) ^ (1 / diagExp p q) := by
  have hm : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  rw [← approximationNumber_zero_eq_norm (DiagCLMpq p q σ),
    approximationNumber_DiagCLMpq_eq hpq hq σ hσ hm, diagTail]
  congr 1
  exact Finset.sum_congr (Finset.filter_true_of_mem fun i _ => Nat.zero_le _) fun _ _ => rfl
end SNumbers
