-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CMGeneralPoint_proof_94c0a01675d2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:53:46.172778+00:00
-- url     : https://prove2.me/submissions/b3790bf5-181e-410f-af3f-0c18a333f5ae

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMGeneralPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCMLocusOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PCMGeneralPoint
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes_a5d964dc9852

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
open MvPolynomial ComplexSets IsLocalRing
namespace GroundTheory.Heights₂.Heights
namespace CMGeneralPoint
theorem _root_.solution (hOpen : CMLocusOpen.Statement) : CMGeneralPoint.Statement := by
  intro n I W hW
  have : W.IsPrime := hW.1.1
  obtain ⟨g, hgW, hg⟩ :=
    hOpen n I W hW.1.2 (isCohenMacaulayLocalRing_atPrime_of_mem_minimalPrimes hW)
  have hfin : (I.minimalPrimes \ {W}).Finite :=
    (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).subset Set.sdiff_subset
  have hsel : ∀ W' ∈ I.minimalPrimes \ {W}, ∃ h, h ∈ W' ∧ h ∉ W := by
    rintro W' ⟨hW', hne⟩
    by_contra hc
    push Not at hc
    exact hne (le_antisymm hc (hW.2 hW'.1 hc))
  choose! h hh using hsel
  refine ⟨g * ∏ W' ∈ hfin.toFinset, h W', ?_, ?_⟩
  · intro hmem
    rcases Ideal.IsPrime.mem_or_mem ‹W.IsPrime› hmem with h1 | h1
    · exact hgW h1
    · obtain ⟨W', hW', h2⟩ := Ideal.IsPrime.prod_mem_iff.mp h1
      exact (hh W' (hfin.mem_toFinset.mp hW')).2 h2
  · intro q hq hf
    rw [map_mul, map_prod] at hf
    have hg0 : eval q g ≠ 0 := left_ne_zero_of_mul hf
    have hp0 := right_ne_zero_of_mul hf
    refine ⟨fun W' hW' hqW' => ?_, ?_⟩
    · by_contra hne
      have hmem : W' ∈ I.minimalPrimes \ {W} := ⟨hW', hne⟩
      exact hp0 (Finset.prod_eq_zero (hfin.mem_toFinset.mpr hmem) (hqW' _ (hh W' hmem).1))
    · have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) :=
        fun x hx => RingHom.mem_ker.mpr (hq x hx)
      exact hg _ (hW.1.2.trans hWq) fun hk => hg0 (RingHom.mem_ker.mp hk)
end CMGeneralPoint
end GroundTheory.Heights₂.Heights
