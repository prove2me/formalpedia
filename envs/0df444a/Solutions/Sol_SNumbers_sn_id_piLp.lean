-- Prove2me | solution 1 for SNumbers.sn_id_piLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:08:08.84292+00:00
-- url     : https://prove2.me/submissions/37c2cacf-4a26-4dfc-af09-0a3bd7c47e79

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
public import Theorems.Thm_SNumbers_finrank_piLp


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsStrictSNumberSequence s) {n : ℕ} (hn : n < m) :
    s (ContinuousLinearMap.id 𝕜 (PiLp p (fun _ : Fin m => 𝕜))) n = 1 :=
  hs.strictly_normalised_at_id n (Module.lt_rank_of_lt_finrank (by rw [finrank_piLp]; exact hn))
end SNumbers
