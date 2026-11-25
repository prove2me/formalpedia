-- Prove2me | solution 1 for SNumbers.norm_idEmbed_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T05:26:44.898502+00:00
-- url     : https://prove2.me/submissions/14b83b19-e4ef-4d58-b18b-6c8da6fd277d

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
public import Theorems.Thm_SNumbers_piLp_norm_le_of_exponent_ge

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
theorem _root_.solution [Nonempty (Fin m)] (hqp : q ≤ p) :
    ‖idEmbed (𝕜 := 𝕜) (m := m) p q‖ ≤ 1 :=
  opNorm_le_bound _ zero_le_one fun x => by
    rw [one_mul]; exact piLp_norm_le_of_exponent_ge hqp (WithLp.ofLp x)
end SNumbers
