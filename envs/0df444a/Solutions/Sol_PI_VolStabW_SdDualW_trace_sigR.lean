-- Prove2me | solution 1 for PI.VolStabW.SdDualW.trace_sigR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:57:17.8248+00:00
-- url     : https://prove2.me/submissions/32b686a6-547e-4dc7-8f9e-ded12d7cb907

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_PosNear
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensAll
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdDual
import Theorems.Thm_PI_VolStabW_SdDualW_trace_one_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdDualW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW PositiveNearLattice SdUniqW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)
variable [FiniteDimensional F E]
namespace PI.VolStabW.SdDualW
theorem _root_.solution (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (w : Fv F v ⊗[F] E) :
    Algebra.trace (Fv F v) (Fv F v ⊗[F] E) (sigR (Fv F v) σ w) =
      Algebra.trace (Fv F v) (Fv F v ⊗[F] E) w := by
  let B := Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E)
  have hB : ∀ k, B k = (1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k := fun k =>
    Algebra.TensorProduct.basis_apply _ _
  let eσ : E ≃ₐ[F] E := AlgEquiv.ofBijective σ
    ⟨σ.toRingHom.injective, fun x => ⟨σ x, hσ x⟩⟩
  have htr : ∀ e : E, Algebra.trace F E (σ e) = Algebra.trace F E e := fun e =>
    Algebra.trace_eq_of_algEquiv eσ e
  conv_lhs => rw [← B.sum_repr w]
  conv_rhs => rw [← B.sum_repr w]
  rw [map_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sigR_smul, map_smul, map_smul, hB]
  have : sigR (Fv F v) σ ((1 : Fv F v) ⊗ₜ[F] (Module.finBasis F E) k) =
      (1 : Fv F v) ⊗ₜ[F] σ ((Module.finBasis F E) k) := by simp [sigR]
  rw [this, trace_one_tmul, trace_one_tmul, htr]
end PI.VolStabW.SdDualW
