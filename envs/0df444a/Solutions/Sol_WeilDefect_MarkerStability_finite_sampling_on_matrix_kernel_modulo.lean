-- Prove2me | solution 1 for WeilDefect.MarkerStability.finite_sampling_on_matrix_kernel_modulo
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-09T18:16:47.341657+00:00
-- url     : https://prove2.me/submissions/ee088807-c871-4685-862f-6b33ea1dea80

import Mathlib.Data.Complex.Basic
import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_determine_all
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import Theorems.Thm_WeilDefect_MarkerStability_finite_functionals_modulo_submodule
set_option autoImplicit false
open Matrix
open scoped Classical
noncomputable section
open WeilDefect.MarkerStability
theorem solution
    {I Ω : Type*} [Fintype I] (K H : Matrix I I ℂ) (r : Ω → (I → ℂ))
    (hHK : LinearMap.ker H.mulVecLin ≤ LinearMap.ker K.mulVecLin)
    (hr : ∀ ρ c, H *ᵥ c = 0 → r ρ ⬝ᵥ c = 0) :
    ∃ G : Finset Ω,
      G.card ≤ Module.finrank ℂ (LinearMap.ker K.mulVecLin) -
        Module.finrank ℂ (LinearMap.ker H.mulVecLin) ∧
      ∀ c : I → ℂ, K *ᵥ c = 0 →
        ((∀ ρ ∈ G, r ρ ⬝ᵥ c = 0) ↔ ∀ ρ : Ω, r ρ ⬝ᵥ c = 0) := by
  let U := LinearMap.ker K.mulVecLin
  let W := (LinearMap.ker H.mulVecLin).comap U.subtype
  let rows : Ω → Module.Dual ℂ U := fun ρ =>
    { toFun := fun c => r ρ ⬝ᵥ c.1
      map_add' := fun _ _ => dotProduct_add _ _ _
      map_smul' := fun _ _ => by simp only [Submodule.coe_smul, dotProduct_smul, RingHom.id_apply] }
  have hz : ∀ ρ, W ≤ LinearMap.ker (rows ρ) := fun ρ c hc => hr ρ c.1 hc
  obtain ⟨G, hcard, hrows⟩ := finite_functionals_modulo_submodule W rows hz
  have hdim : Module.finrank ℂ W = Module.finrank ℂ (LinearMap.ker H.mulVecLin) :=
    (Submodule.comapSubtypeEquivOfLe hHK).finrank_eq
  have hquot : Module.finrank ℂ (U ⧸ W) = Module.finrank ℂ U -
      Module.finrank ℂ (LinearMap.ker H.mulVecLin) := by
    rw [← hdim]
    exact Nat.eq_sub_of_add_eq W.finrank_quotient_add_finrank
  refine ⟨G, ?_, fun c hc => hrows ⟨c, hc⟩⟩
  simpa only [hquot] using hcard
