-- Prove2me | solution 1 for PI.SqPairLocal.StModel.exists_clear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:15:33.015933+00:00
-- url     : https://prove2.me/submissions/da9d660d-eddf-4423-bdbb-66cc0bb0b912

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_IntAtOfDivAtZero
import Theorems.Thm_P2M_PI_SqPairLocal_StModel___ne_57ec0e9aa56c

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
open PI.SqPairLocal.StModel
variable {Q : Ideal (𝓞 E)} (M : StModel E Q)
namespace PI.SqPairLocal.StModel
theorem _root_.solution [hQ : Q.IsPrime] {ι : Type} [Fintype ι] (x : ι → E) :
    ∃ k : ℕ, ∃ t : 𝓞 E, t ∉ Q ∧ ∃ w : ι → 𝓞 E,
      ∀ i, algebraMap (𝓞 E) E t * algebraMap (𝓞 E) E M.ϖ ^ k * x i = algebraMap (𝓞 E) E (w i) := by
  classical
  have hϖ0 : M.ϖ ≠ 0 := M.ϖ_ne
  have hQ0 : Q ≠ ⊥ := fun h => hϖ0 ((Submodule.eq_bot_iff Q).mp h _ M.ϖ_Q)
  obtain ⟨⟨D, hD⟩, hint⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 E)) Finset.univ x
  have hint' : ∀ i, ∃ a : 𝓞 E, algebraMap (𝓞 E) E a = D • x i := fun i => hint i (Finset.mem_univ i)
  choose a ha using hint'
  have hD0 : D ≠ 0 := nonZeroDivisors.ne_zero hD
  obtain ⟨k, t, ht, r, hr⟩ : ∃ k : ℕ, ∃ t : 𝓞 E, t ∉ Q ∧ ∃ r : 𝓞 E, t * M.ϖ ^ k = D * r := by
    haveI : IsDiscreteValuationRing (Localization.AtPrime Q) := by
      first
        | exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _
        | infer_instance
    have hinj : Function.Injective (algebraMap (𝓞 E) (Localization.AtPrime Q)) :=
      IsLocalization.injective _ (Ideal.primeCompl_le_nonZeroDivisors Q)
    have hne : ∀ c : 𝓞 E, c ≠ 0 → algebraMap (𝓞 E) (Localization.AtPrime Q) c ≠ 0 := fun c hc h0 =>
      hc (hinj (by rw [h0, map_zero]))
    have hϖm : algebraMap (𝓞 E) (Localization.AtPrime Q) M.ϖ ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime Q) := by
      first
        | exact (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime Q) Q M.ϖ).mpr M.ϖ_Q
        | (rw [← Localization.AtPrime.map_eq_maximalIdeal]; exact Ideal.mem_map_of_mem _ M.ϖ_Q)
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne D hD0) hπ
    obtain ⟨m, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne M.ϖ hϖ0) hπ
    have hm : m ≠ 0 := by
      rintro rfl
      apply (IsLocalRing.mem_maximalIdeal _).mp hϖm
      rw [hu', pow_zero, mul_one]; exact u'.isUnit
    have hdvd : algebraMap (𝓞 E) (Localization.AtPrime Q) D ∣
        algebraMap (𝓞 E) (Localization.AtPrime Q) M.ϖ ^ n := by
      rw [hu, hu', mul_pow, ← pow_mul]
      exact mul_dvd_mul u.isUnit.dvd (pow_dvd_pow π (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm)))
    obtain ⟨y, hy⟩ := hdvd
    obtain ⟨⟨r, t, htQ⟩, hrt⟩ := IsLocalization.surj Q.primeCompl y
    have hrt' : y * algebraMap (𝓞 E) (Localization.AtPrime Q) t = algebraMap (𝓞 E) (Localization.AtPrime Q) r := hrt
    refine ⟨n, t, htQ, r, hinj ?_⟩
    rw [map_mul, map_mul, map_pow, mul_comm (algebraMap (𝓞 E) (Localization.AtPrime Q) t), hy, mul_assoc, hrt']
  refine ⟨k, t, ht, fun i => r * a i, fun i => ?_⟩
  have hr' := congrArg (algebraMap (𝓞 E) E) hr
  rw [map_mul, map_pow, map_mul] at hr'
  rw [map_mul, ha i, Algebra.smul_def, hr']
  ring
end PI.SqPairLocal.StModel
