-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.ChiExCM.kron_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:38:07.797798+00:00
-- url     : https://prove2.me/submissions/ed32a462-e111-4a00-aa0a-44ec3155d4cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ChiExCM
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_CharExtend
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_NormOneCharacters_NormOneCharacterApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.ChiExCM
open NumberField
variable {E : Type} [Field E] [NumberField E]
namespace PI.UnitaryGroupMassFormula.ChiExCM
theorem _root_.solution (c : E →+* E) (hc : ∀ (φ : E →+* ℂ) (x : E), φ (c x) = (starRingEnd ℂ) (φ x))
    (u : E) (hu : u * c u = 1) (h1 : Submodule.span (𝓞 E) {u} = 1) : ∃ m : ℕ, 0 < m ∧ u ^ m = 1 := by
  rw [Submodule.one_eq_span, Submodule.span_singleton_eq_span_singleton] at h1
  obtain ⟨a, ha⟩ := h1
  rw [Units.smul_def, Algebra.smul_def] at ha
  have h3 : algebraMap (𝓞 E) E (a : 𝓞 E) * algebraMap (𝓞 E) E ((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hu' : u = algebraMap (𝓞 E) E ((a⁻¹ : (𝓞 E)ˣ) : 𝓞 E) :=
    mul_left_cancel₀ (left_ne_zero_of_mul_eq_one ha) (ha.trans h3.symm)
  have hint : IsIntegral ℤ u := by rw [hu']; exact RingOfIntegers.isIntegral_coe _
  have hn : ∀ φ : E →+* ℂ, ‖φ u‖ = 1 := by
    intro φ
    have h4 : φ u * (starRingEnd ℂ) (φ u) = 1 := by rw [← hc, ← map_mul, hu, map_one]
    rw [Complex.mul_conj'] at h4
    have h5 : ‖φ u‖ ^ 2 = 1 := by exact_mod_cast h4
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h5
  obtain ⟨n, hn0, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one (K := E) (A := ℂ) hint hn
  exact ⟨n, hn0, hpow⟩
end PI.UnitaryGroupMassFormula.ChiExCM
