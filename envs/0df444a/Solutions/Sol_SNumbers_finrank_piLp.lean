-- Prove2me | solution 1 for SNumbers.finrank_piLp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:02:01.003142+00:00
-- url     : https://prove2.me/submissions/1a4790bd-08fc-43bb-bed5-5dd5599abf5f

module
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Definitions.Def_SNumbers_PiLpCoordinates

set_option autoImplicit true
@[expose] public section
public section
universe u
open scoped ENNReal
open ContinuousLinearMap
open SNumbers
variable {𝕜 : Type u} [RCLike 𝕜] {m : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]
omit [Fact (1 ≤ p)]
namespace SNumbers
theorem _root_.solution (k : ℕ) :
    Module.finrank 𝕜 (PiLp p (fun _ : Fin k => 𝕜)) = k := by
  rw [(WithLp.linearEquiv p 𝕜 (Fin k → 𝕜)).finrank_eq, Module.finrank_pi 𝕜, Fintype.card_fin]
end SNumbers
