-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormReduced_proof_f8e587a11564
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:45:39.596892+00:00
-- url     : https://prove2.me/submissions/b3e56dc1-7d12-441c-a75f-8e058f3992f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsBaseChange
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LocalMultRadical
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsIncIdealSeparate
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PChowFormReduced
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_incIdeal_iffR_6f31959e16f5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_incidence_mono_64f19830bda4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_exists_relComps_of_mem_incidence_6d6a634b74a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_support_fundCycle_iff_47043e9aed45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_fundCycle_apply_of_isRadical_cfa81f886234
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_of_mem_support_fundCycle_dd2dcd3ea52a


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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChowFormReduced
theorem _root_.solution (hPrime : IncIdealPrime.Statement) (hSep : IncIdealSeparate.Statement) :
    ChowFormReduced.Statement := by
  classical
  intro F _ n k J h hJh hJr hch
  have hproj : ∀ W ∈ (fundCycle J).support, IsProjPrime W :=
    fun W hW => isProjPrime_of_mem_support_fundCycle hJh hW
  have hrel : ∀ W ∈ (fundCycle J).support, W ∈ relComps J :=
    fun W hW => (mem_support_fundCycle_iff hJr).mp hW

  have hspan : ∀ g, h ∣ g ↔ ∀ W ∈ (fundCycle J).support, g ∈ incIdeal W k := by
    intro g
    rw [← hch.2 g]
    constructor
    · intro hg W hW
      exact mem_incIdeal_iffR.mpr fun u hu => hg u (incidence_mono (hrel W hW).1.1.2 hu)
    · intro hg u hu
      obtain ⟨W, hW, huW⟩ := exists_relComps_of_mem_incidence hu
      exact mem_incIdeal_iffR.mp (hg W ((mem_support_fundCycle_iff hJr).mpr hW)) u huW

  have hsep : ∀ W ∈ (fundCycle J).support, ∀ W' ∈ (fundCycle J).support,
      incIdeal W' k ≤ incIdeal W k → W' = W := by
    intro W hW W' hW' hle
    have hne : incIdeal W' k ≠ ⊥ := fun hb => hch.1 (by
      have := (hspan h).mp dvd_rfl W' hW'
      rwa [hb, Ideal.mem_bot] at this)
    have hWW' : W' ≤ W := hSep F n k W W' (hproj W hW) (hproj W' hW') hne hle
    exact le_antisymm hWW' ((hrel W hW).1.2 (hrel W' hW').1.1 hWW')

  have hprin : ∀ W ∈ (fundCycle J).support, ∃ q, Prime q ∧ incIdeal W k = Ideal.span {q} := by
    intro W hW
    have hPW : (incIdeal W k).IsPrime := hPrime F n k W (hproj W hW).isPrime (hproj W hW).isRelevant
    have hhW : h ∈ incIdeal W k := (hspan h).mp dvd_rfl W hW
    obtain ⟨u, hu⟩ := UniqueFactorizationMonoid.factors_prod hch.1
    have hprod : (UniqueFactorizationMonoid.factors h).prod ∈ incIdeal W k := by
      rwa [← hu, Ideal.mul_unit_mem_iff_mem _ u.isUnit] at hhW
    obtain ⟨q, hqf, hqW⟩ := (hPW.multiset_prod_mem_iff_exists_mem _).1 hprod
    have hq : Prime q := UniqueFactorizationMonoid.prime_of_factor q hqf
    have hqh : q ∣ h := UniqueFactorizationMonoid.dvd_of_mem_factors hqf
    have hqle : Ideal.span {q} ≤ incIdeal W k := (Ideal.span_singleton_le_iff_mem _).mpr hqW
    refine ⟨q, hq, le_antisymm ?_ hqle⟩
    have hqP : (Ideal.span {q}).IsPrime := (Ideal.span_singleton_prime hq.ne_zero).mpr hq
    have hinf : (fundCycle J).support.inf (fun W' => incIdeal W' k) ≤ Ideal.span {q} := by
      intro g hg
      rw [Ideal.mem_span_singleton]
      exact dvd_trans hqh ((hspan g).mpr fun W' hW' =>
        Finset.inf_le (f := fun W' => incIdeal W' k) hW' hg)
    obtain ⟨W', hW', hle⟩ := hqP.inf_le'.mp hinf
    have hW'W : W' = W := hsep W hW W' hW' (hle.trans hqle)
    rw [← hW'W]
    exact hle
  choose! q hq hqspan using hprin

  have hdvd₁ : (∏ W ∈ (fundCycle J).support, q W) ∣ h := by
    refine Finset.prod_dvd_of_isRelPrime ?_ fun W hW => ?_
    · intro W hW W' hW' hne
      refine (hq W hW).irreducible.isRelPrime_iff_not_dvd.mpr fun hdvd => hne ?_
      have hmem : q W' ∈ incIdeal W k := by
        rw [hqspan W hW]
        exact Ideal.mem_span_singleton.mpr hdvd
      refine (hsep W hW W' hW' ?_).symm
      rw [hqspan W' hW']
      exact (Ideal.span_singleton_le_iff_mem _).mpr hmem
    · have := (hspan h).mp dvd_rfl W hW
      rw [hqspan W hW] at this
      exact Ideal.mem_span_singleton.mp this
  have hdvd₂ : h ∣ ∏ W ∈ (fundCycle J).support, q W := by
    refine (hspan _).mpr fun W hW => ?_
    rw [hqspan W hW]
    exact Ideal.mem_span_singleton.mpr (Finset.dvd_prod_of_mem q hW)
  obtain ⟨u, hu⟩ := associated_of_dvd_dvd hdvd₁ hdvd₂
  obtain ⟨r, hr, hur⟩ := (isUnit_iff_eq_C_of_isReduced (P := (u : MvPolynomial (Fin k × Fin n) F))).mp
    u.isUnit
  refine ⟨r, hr.ne_zero, q, fun W hW => ⟨(hq W hW).ne_zero, fun g => ?_⟩, ?_⟩
  · rw [← mem_incIdeal_iffR, hqspan W hW, Ideal.mem_span_singleton]
  · rw [Finset.prod_congr rfl fun W hW => by rw [fundCycle_apply_of_isRadical hJr hW, pow_one],
      ← hu, hur, mul_comm]
end ChowFormReduced
end GroundTheory.Heights₂.Heights
