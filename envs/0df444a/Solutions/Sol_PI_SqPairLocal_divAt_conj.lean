-- Prove2me | solution 1 for PI.SqPairLocal.divAt_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:23:08.096216+00:00
-- url     : https://prove2.me/submissions/91aa5507-9a9e-4a2f-bfeb-a2a0bf336c84

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField Matrix
open PI PI.SqPairLocal
open PI.SqPair
attribute [local instance] StModel.cr StModel.dom StModel.dvr StModel.hens StModel.fin
variable {E : Type} [Field E] [NumberField E] [StarRing E]
namespace PI.SqPairLocal
theorem _root_.solution {Q : Ideal (𝓞 E)} [hQ : Q.IsPrime] {N : ℕ} (ϖ d : 𝓞 E) (hϖ : ϖ ≠ 0)
    (hd : d ∉ Q) (k m : ℕ) (G : Matrix (Fin N) (Fin N) (𝓞 E)) (X : Matrix (Fin N) (Fin N) E)
    (hGX : ∀ a b, algebraMap (𝓞 E) E (G a b) =
      algebraMap (𝓞 E) E d * algebraMap (𝓞 E) E ϖ ^ (2 * k) * X a b)
    (h : ∀ a b, ∃ s : 𝓞 E, s ∉ Q ∧ ∃ w : 𝓞 E, s * G a b = ϖ ^ (2 * k + m) * w) (a b : Fin N) :
    DivAt Q (ϖ ^ m) (X a b) := by
  obtain ⟨s, hs, w, hw⟩ := h a b
  refine ⟨s * d, fun hm => (hQ.mem_or_mem hm).elim hs hd, w, ?_⟩
  have h2 := congrArg (algebraMap (𝓞 E) E) hw
  simp only [map_mul, map_pow, hGX, pow_add] at h2
  have hϖE : algebraMap (𝓞 E) E ϖ ≠ 0 := by
    intro h0
    apply hϖ
    first
      | exact (map_eq_zero_iff _ (NoZeroSMulDivisors.algebraMap_injective (𝓞 E) E)).mp h0
      | exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).mp h0
      | exact_mod_cast h0
  have hp : algebraMap (𝓞 E) E ϖ ^ (2 * k) ≠ 0 := pow_ne_zero _ hϖE
  have h3 : algebraMap (𝓞 E) E ϖ ^ (2 * k) *
      (algebraMap (𝓞 E) E s * algebraMap (𝓞 E) E d * X a b) =
      algebraMap (𝓞 E) E ϖ ^ (2 * k) * (algebraMap (𝓞 E) E ϖ ^ m * algebraMap (𝓞 E) E w) := by
    linear_combination h2
  have h4 := mul_left_cancel₀ hp h3
  show algebraMap (𝓞 E) E (s * d) * X a b = algebraMap (𝓞 E) E (ϖ ^ m) * algebraMap (𝓞 E) E w
  rw [map_mul, map_pow]
  exact h4
end PI.SqPairLocal
