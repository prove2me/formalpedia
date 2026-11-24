-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_TorsionFreeQuotientLength_length_pi_quot_smul_top_69b4b0f38899
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:07:42.233943+00:00
-- url     : https://prove2.me/submissions/7c823a78-837e-4488-97c6-b5216ba71e6c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Module Submodule
open scoped Pointwise
open GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
theorem _root_.solution (t : ℕ) (a : R) :
    Module.length R ((Fin t → R) ⧸ (a • ⊤ : Submodule R (Fin t → R))) =
      t * Module.length R (R ⧸ Ideal.span {a}) := by
  let f : (Fin t → R) →ₗ[R] (Fin t → R ⧸ Ideal.span {a}) :=
    LinearMap.pi fun i => (Ideal.span {a}).mkQ ∘ₗ LinearMap.proj i
  have hf : Function.Surjective f := by
    intro y
    choose g hg using fun i => Ideal.Quotient.mk_surjective (y i)
    exact ⟨g, funext fun i => by simp [f, hg i]⟩
  have hker : LinearMap.ker f = a • ⊤ := by
    ext x
    simp only [LinearMap.mem_ker, Submodule.mem_smul_pointwise_iff_exists, Submodule.mem_top,
      true_and]
    constructor
    · intro h
      have hx : ∀ i, x i ∈ Ideal.span {a} := fun i => by
        have := congrFun h i
        exact Ideal.Quotient.eq_zero_iff_mem.mp (by simpa [f] using this)
      choose c hc using fun i => Ideal.mem_span_singleton'.mp (hx i)
      exact ⟨c, funext fun i => by simp [← hc i, mul_comm]⟩
    · rintro ⟨b, rfl⟩
      funext i
      simp only [f, LinearMap.pi_apply, LinearMap.coe_comp, Function.comp_apply, Pi.smul_apply,
        LinearMap.coe_proj, Function.eval, mkQ_apply, Pi.zero_apply]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a))
  rw [← hker, (f.quotKerEquivOfSurjective hf).length_eq, Module.length_pi]
  simp
end GroundTheory.Heights₂.Heights.Model.TorsionFreeQuotientLength
