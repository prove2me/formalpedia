-- Prove2me | solution 1 for SNumbers.kolmogorovNumber_DiagCLM_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:04:54.01022+00:00
-- url     : https://prove2.me/submissions/5266971a-b53e-4507-a2c5-13adfa730608

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
public import Theorems.Thm_SNumbers_sn_DiagCLM_eq
public import Theorems.Thm_SNumbers_isStrictSNumberSequence_kolmogorovNumber


set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution {σ : Fin m → 𝕜}
    (hσ : _root_.Antitone fun i => ‖σ i‖) {n : ℕ} (hn : n < m) :
    kolmogorovNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_kolmogorovNumber hσ hn
end SNumbers
