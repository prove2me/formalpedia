-- Prove2me | solution 1 for SNumbers.sn_DiagCLM_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T04:03:09.354202+00:00
-- url     : https://prove2.me/submissions/75ab4922-d8b9-4582-8a78-c7eba6ba789a

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
public import Theorems.Thm_SNumbers_sn_le_approximationNumber


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution {s : Family 𝕜} (hs : IsStrictSNumberSequence s)
    {σ : Fin m → 𝕜} (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    s (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  le_antisymm
    ((sn_le_approximationNumber hs.toIsSNumberSequence (DiagCLM p σ) n).trans
      (approximationNumber_DiagCLM_le hσ hn))
    (le_sn_DiagCLM hs hσ hn)
end SNumbers
