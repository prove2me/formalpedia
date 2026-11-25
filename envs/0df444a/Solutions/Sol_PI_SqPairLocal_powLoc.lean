-- Prove2me | solution 1 for PI.SqPairLocal.powLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:23:07.832375+00:00
-- url     : https://prove2.me/submissions/90efc6dc-e034-4ccc-9944-392ee0604d15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_SqPairLocalOfSteps
import Definitions.Def_Lemmata_GeneralBFactLeftBis_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarePairLocal_ExistsDenFg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.SqPairLocal
open PI.SqPair Formalism.L2.PairingIndexBounds.Eq.SqG
namespace PI.SqPairLocal
theorem _root_.solution : PowLoc := by
  intro E _ _ Q hQ c hc
  have := hQ.isPrime
  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (NumberField.RingOfIntegers.not_isField E)
  have : IsDiscreteValuationRing (Localization.AtPrime Q) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 E) hQ0 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime Q)
  have hc' : algebraMap (𝓞 E) (Localization.AtPrime Q) c ≠ 0 := by
    intro h
    apply hc
    apply IsLocalization.injective (Localization.AtPrime Q) (Ideal.primeCompl_le_nonZeroDivisors Q)
    rw [h, map_zero]
  obtain ⟨K, hK⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {algebraMap (𝓞 E) (Localization.AtPrime Q) c})
    (by rwa [Ne, Ideal.span_singleton_eq_bot]) hϖ
  refine ⟨K, fun x hx => ?_⟩
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime Q) = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hxA : algebraMap (𝓞 E) (Localization.AtPrime Q) x ∈
      Ideal.span {algebraMap (𝓞 E) (Localization.AtPrime Q) c} := by
    rw [hK, ← Ideal.span_singleton_pow, ← hmax,
      ← IsLocalization.AtPrime.map_eq_maximalIdeal (p := Q), ← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hx
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp hxA
  obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective Q.primeCompl y
  have key : algebraMap (𝓞 E) (Localization.AtPrime Q) (c * w) =
      algebraMap (𝓞 E) (Localization.AtPrime Q) (s * x) := by
    rw [map_mul, map_mul, ← hy, ← IsLocalization.mk'_spec (Localization.AtPrime Q) w s]
    ring
  obtain ⟨t, ht⟩ := (IsLocalization.eq_iff_exists Q.primeCompl (Localization.AtPrime Q)).mp key
  refine ⟨(t * s : Q.primeCompl), (t * s : Q.primeCompl).2, t * w, ?_⟩
  push_cast
  linear_combination -ht
end PI.SqPairLocal
