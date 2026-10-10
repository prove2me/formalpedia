-- Prove2me | solution 1 for WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T17:27:15.197331+00:00
-- url     : https://prove2.me/submissions/6ce2fc7f-b84f-499c-a0a0-46970e422881

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin

import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_determine_all
set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section
open WeilDefect.MarkerStability
theorem solution
    {I Ω : Type*} [Fintype I] (K : Matrix I I ℂ) (r : Ω → (I → ℂ)) :
    ∃ G : Finset Ω, G.card ≤ Module.finrank ℂ (LinearMap.ker K.mulVecLin) ∧
      ∀ c : I → ℂ, K *ᵥ c = 0 →
        ((∀ ρ ∈ G, r ρ ⬝ᵥ c = 0) ↔ ∀ ρ : Ω, r ρ ⬝ᵥ c = 0) := by
  let rows : Ω → Module.Dual ℂ (LinearMap.ker K.mulVecLin) := fun ρ =>
    { toFun := fun c => r ρ ⬝ᵥ c.1
      map_add' := fun _ _ => dotProduct_add _ _ _
      map_smul' := fun _ _ => by simp only [Submodule.coe_smul, dotProduct_smul, RingHom.id_apply] }
  obtain ⟨G, hcard, hrows⟩ := finite_functionals_determine_all rows
  exact ⟨G, hcard, fun c hc => hrows ⟨c, hc⟩⟩
