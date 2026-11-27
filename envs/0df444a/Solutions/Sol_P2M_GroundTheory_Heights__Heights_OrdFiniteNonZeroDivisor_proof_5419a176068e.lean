-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrdFiniteNonZeroDivisor_proof_5419a176068e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:08:00.243264+00:00
-- url     : https://prove2.me/submissions/f02fe52e-27b7-4beb-ab30-cfcb868ca904

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StOrdFiniteNonZeroDivisor
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_CurveNormalisationFiniteLemmas
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_POrdFiniteNonZeroDivisor
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isLocalRing_curveLocalRing_1a14dd5b926d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_algebraMap_curveNormalisation_injective_fe83821bff87
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isReduced_curveLocalRing_913d64c72495


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial ComplexSets
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace OrdFiniteNonZeroDivisor
theorem _root_.solution : OrdFiniteNonZeroDivisor.Statement := by
  intro n I q f hrad hdim hord
  have : Nontrivial (curveLocalRing I q) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact WithBot.bot_ne_coe hdim
  have : IsLocalRing (curveLocalRing I q) := isLocalRing_curveLocalRing I q
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  rw [mem_nonZeroDivisors_iff_right]
  intro y hyx
  by_contra hy

  obtain ⟨p, hp, hyp⟩ : ∃ p ∈ minimalPrimes (curveLocalRing I q), y ∉ p := by
    have : y ∉ (⊥ : Ideal (curveLocalRing I q)).radical := by
      rintro ⟨k, hk⟩
      exact hy (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
    simpa [← Ideal.sInf_minimalPrimes, minimalPrimes] using this
  have hpP : p.IsPrime := hp.1.1
  have hxp := (hpP.mem_or_mem (hyx ▸ p.zero_mem)).resolve_left hyp

  have hpmax : ¬ p.IsMaximal := by
    intro hm
    have h1 := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := curveLocalRing I q)
    rw [← IsLocalRing.eq_maximalIdeal hm, Ideal.height_eq_zero_iff.mpr hp, hdim] at h1
    exact absurd h1 (by decide)

  have : Algebra.IsIntegral (curveLocalRing I q) (curveNormalisation I q) :=
    inferInstanceAs (Algebra.IsIntegral (curveLocalRing I q)
      (integralClosure (curveLocalRing I q) (FractionRing (curveLocalRing I q))))
  obtain ⟨Q, -, hQ, hQp⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal (curveNormalisation I q))
    (by rw [← RingHom.ker_eq_comap_bot, (RingHom.injective_iff_ker_eq_bot _).1
      (algebraMap_curveNormalisation_injective I q)]; exact bot_le)
  obtain ⟨P, hPm, hQP⟩ := Ideal.exists_le_maximal Q hQ.ne_top
  apply hord ⟨P, hPm⟩
  have : P.IsPrime := hPm.isPrime
  have hd : Disjoint (P.primeCompl : Set (curveNormalisation I q)) Q :=
    Set.disjoint_left.2 fun a ha haQ ↦ ha (hQP haQ)
  set Q' := Q.map (algebraMap (curveNormalisation I q) (Localization.AtPrime P)) with hQ'def
  have : Q'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint P.primeCompl _ Q hQ hd
  have hQ'u : Q'.under _ = Q := IsLocalization.under_map_of_isPrime_disjoint P.primeCompl _ hQ hd
  have hle : Ideal.span {algebraMap (curveNormalisation I q) (Localization.AtPrime P)
      (algebraMap (curveLocalRing I q) (curveNormalisation I q)
        (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))} ≤ Q' := by
    rw [Ideal.span_singleton_le_iff_mem]
    refine Ideal.mem_map_of_mem _ ?_
    rw [← hQp] at hxp
    exact hxp

  change Module.length (Localization.AtPrime P) (Localization.AtPrime P ⧸ Ideal.span {_}) = ⊤
  by_contra hne
  rw [← ne_eq, Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hne
  obtain ⟨-, hart⟩ := hne
  have : IsArtinian (Localization.AtPrime P) (Localization.AtPrime P ⧸ Q') :=
    isArtinian_of_surjective _ (Submodule.factor hle) (Submodule.factor_surjective hle)
  have : IsArtinianRing (Localization.AtPrime P ⧸ Q') := isArtinian_of_tower (Localization.AtPrime P) this
  have hQ'max : Q'.IsMaximal :=
    Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)
  have hQeq : Q = P := by
    rw [← hQ'u, IsLocalRing.eq_maximalIdeal hQ'max, Localization.AtPrime.under_maximalIdeal]
  apply hpmax
  rw [← hQp]
  have : Q.IsMaximal := hQeq ▸ hPm
  exact Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
end OrdFiniteNonZeroDivisor
end GroundTheory.Heights₂.Heights
