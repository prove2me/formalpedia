-- Prove2me | solution 1 for PIW.AdelicOrbitU.decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:19:40.748798+00:00
-- url     : https://prove2.me/submissions/675b69f8-40aa-46de-b69b-1dda8dfdd71e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_StLamOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
variable (R : Type) [CommRing R] [Algebra F R]
namespace PIW.AdelicOrbitU
theorem _root_.solution (θ : E) (hspan : ∀ e : E, ∃ p q : F, e = algebraMap F E p + algebraMap F E q * θ)
    (z : R ⊗[F] E) : ∃ a b : R, z = algebraMap R (R ⊗[F] E) a + algebraMap R (R ⊗[F] E) b * (1 ⊗ₜ θ) := by
  have hidR : ∀ x : R, algebraMap R R x = x := fun _ => rfl
  induction z using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul r x =>
    obtain ⟨p, q, rfl⟩ := hspan x
    refine ⟨p • r, q • r, ?_⟩
    simp only [Algebra.TensorProduct.algebraMap_apply, hidR,
      Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, TensorProduct.tmul_add]
    rw [TensorProduct.smul_tmul, TensorProduct.smul_tmul, Algebra.smul_def, Algebra.smul_def, mul_one]
  | add x y hx hy =>
    obtain ⟨a1, b1, rfl⟩ := hx
    obtain ⟨a2, b2, rfl⟩ := hy
    refine ⟨a1 + a2, b1 + b2, ?_⟩
    rw [map_add, map_add]
    ring
end PIW.AdelicOrbitU
