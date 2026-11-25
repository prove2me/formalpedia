-- Prove2me | solution 1 for SNumbers.approximationNumber_idEmbed_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:23:42.523941+00:00
-- url     : https://prove2.me/submissions/40d5b03b-5602-4e44-9023-02a1953d5510

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity
public import Theorems.Thm_SNumbers_approximationNumber_idEmbed_le
public import Theorems.Thm_SNumbers_le_approximationNumber_idEmbed

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
    (hpq : p ≤ q) (hq : q ≠ ∞) {n : ℕ} (hn : n < m) :
    approximationNumber (idEmbed (𝕜 := 𝕜) (m := m) p q) n
      = ((m - n : ℕ) : ℝ) ^ (1 / p.toReal - 1 / q.toReal) :=
  le_antisymm (approximationNumber_idEmbed_le hpq hq hn.le) (le_approximationNumber_idEmbed hpq hq hn)
end SNumbers
