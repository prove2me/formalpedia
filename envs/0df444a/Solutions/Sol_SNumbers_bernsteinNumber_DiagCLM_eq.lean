-- Prove2me | solution 1 for SNumbers.bernsteinNumber_DiagCLM_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T06:07:23.310739+00:00
-- url     : https://prove2.me/submissions/e9ba0536-e95e-417a-a822-bcabc8dc9cae

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
public import Theorems.Thm_SNumbers_isStrictSNumberSequence_bernsteinNumber


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
    bernsteinNumber (DiagCLM p σ) n = ‖σ ⟨n, hn⟩‖ :=
  sn_DiagCLM_eq isStrictSNumberSequence_bernsteinNumber hσ hn
end SNumbers
