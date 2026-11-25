-- Prove2me | solution 1 for SNumbers.idEmbed_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:46:22.103103+00:00
-- url     : https://prove2.me/submissions/ab2f0c27-b2f8-4903-8789-f42cd504add4

module
public import Definitions.Def_SNumbers_Approximation
public import Definitions.Def_SNumbers_Examples_FlatnessLemmas
public import Mathlib.Analysis.MeanInequalities
public import Definitions.Def_SNumbers_Examples_Identity

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
    (x : PiLp q (fun _ : Fin m => 𝕜)) (i : Fin m) : (idEmbed p q x) i = x i := rfl
end SNumbers
