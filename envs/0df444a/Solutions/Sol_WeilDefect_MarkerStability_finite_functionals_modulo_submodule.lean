-- Prove2me | solution 1 for WeilDefect.MarkerStability.finite_functionals_modulo_submodule
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T18:15:41.323248+00:00
-- url     : https://prove2.me/submissions/407834c7-b698-49d6-b105-477ffe291804

import Mathlib.Data.Complex.Basic
import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_determine_all
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section
open WeilDefect.MarkerStability
theorem solution
    {V Ω : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (W : Submodule ℂ V) (r : Ω → Module.Dual ℂ V)
    (hr : ∀ ρ, W ≤ LinearMap.ker (r ρ)) :
    ∃ G : Finset Ω, G.card ≤ Module.finrank ℂ (V ⧸ W) ∧
      ∀ v : V, (∀ ρ ∈ G, r ρ v = 0) ↔ ∀ ρ : Ω, r ρ v = 0 := by
  obtain ⟨G, hcard, hrows⟩ := finite_functionals_determine_all
    (fun ρ => W.liftQ (r ρ) (hr ρ))
  exact ⟨G, hcard, fun v => hrows (W.mkQ v)⟩
