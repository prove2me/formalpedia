-- Prove2me | solution 1 for PI.AprimeInfW.mp_of_isom_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:34:01.831895+00:00
-- url     : https://prove2.me/submissions/fdf0f97c-85b3-4911-9884-117aaf612f6d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_DetMulRCReal
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_MpOfIsomProd
import Theorems.Thm_PI_AprimeInfW_mp_of_isom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW
open MeasureTheory Matrix ComplexConjugate
variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
variable {U V : Type} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [MeasurableSpace U] [BorelSpace U] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace PI.AprimeInfW
theorem _root_.solution (f : U × V →ₗ[ℝ] F) (hn : ∀ a b, ‖f (a, b)‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2)
    (hs : Function.Surjective f) : MeasurePreserving f volume volume := by
  let L : WithLp 2 (U × V) ≃ₗ[ℝ] U × V := WithLp.linearEquiv 2 ℝ (U × V)
  have h1 : MeasurePreserving (f.comp L.toLinearMap) volume volume := by
    apply mp_of_isom
    · intro t
      have h := hn (L t).1 (L t).2
      have h2 := WithLp.prod_norm_sq_eq_of_L2 t
      have e : (L t) = ((L t).1, (L t).2) := rfl
      rw [← e] at h
      have h3 : ‖f (L t)‖ ^ 2 = ‖t‖ ^ 2 := by rw [h, h2]; rfl
      exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h3
    · exact hs.comp L.surjective
  have h2 := WithLp.volume_preserving_toLp U V
  have h3 : (⇑(f.comp L.toLinearMap) ∘ WithLp.toLp 2) = ⇑f := by
    funext x
    rfl
  have h4 := h1.comp h2
  rwa [h3] at h4
end PI.AprimeInfW
