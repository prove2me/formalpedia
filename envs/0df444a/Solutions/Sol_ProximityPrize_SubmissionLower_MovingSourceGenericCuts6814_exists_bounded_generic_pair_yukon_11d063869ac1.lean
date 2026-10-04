-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.exists_bounded_generic_pair_yukon_11d063869ac1
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T01:54:51.816929+00:00
-- url     : https://prove2.me/submissions/2de3702a-e2c6-472c-8a58-c6291cbd9f53

import Definitions.Def_Yukon_6db579f0800634a21a2958ad



import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceGenericCuts6814_normalized_target_flag_yukon_8a92d1b35601
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
import Definitions.Def_Yukon_cab3e47590aea7a2fd8756f8
import Definitions.Def_Yukon_10805ee98000946934f31f50
import Definitions.Def_Yukon_f9b1aa1ba67da67faf9565ef
import Definitions.Def_Yukon_6d3add3a3f6938cc0bdd10e2
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.normalized_target_flag := @ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.normalized_target_flag_yukon_8a92d1b35601
namespace ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814
end MovingSourceCoprimeCuts6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceClearing6814
end MovingSourceClearing6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN207
end RCN207
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN135
end RCN135
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN095
end RCN095
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN095 RCN135 RCN136 RCN207
open MovingSourceClearing6814 MovingSourceCoprimeCuts6814
variable (E : Type*) [Field E]
section ActualPair
variable {K : Type*} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField Omega
local notation "Poly3" => MvPolynomial (Fin 3) Omega
local notation "Poly3T" => MvPolynomial (Fin 3) OmegaT
/-- Actual nonzero coprime generic moving cuts, with the claimed flags
and the exact regular-locus zero correspondence. This is the algebraic
input to the remaining shared curve-family degree/pole count. -/
theorem _root_.solution
    (J Q : WholeSpaceCube6814.Poly (K := K))
    (hJ : J≠0) (hQ : Q≠0) (hrel : IsRelPrime J Q)
    (hJdegree : J.degreeOf 1 ≤ 2) (hQdegree : Q.degreeOf 1 ≤ 14)
    (U T : ℕ) (hJU : 9 ≤ U) (hUT : U ≤ T)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3 ≤ 9 ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (hQbounds : ∀ e ∈ Q.support, 2*e 1+e 3 ≤ 31 ∧ e 1+e 2+e 3 ≤ 98 ∧ e 1+e 2+e 3+e 4 ≤ 1700)
    (quadratic A : Poly3) (hden : (2 : Poly3)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic)
    (hAflag : PolynomialInFlag unitYZFlag A) :
    ∃ B C : Poly3T, B≠0 ∧ C≠0 ∧ IsRelPrime B C ∧
      PolynomialInFlag ⟨T-U,U-9+2,9⟩ B ∧ PolynomialInFlag ⟨1602,81,31⟩ C ∧
      ∀ (L : Type*) [Field L] (ev : Poly3T →+* L),
        ev (MvPolynomial.map (coefficientEmbedding Omega) (2*A))≠0 →
        ((ev B=0 ↔ ev (movingCut ((coefficientEmbedding Omega).comp (polynomialEmbedding K)) J 2
            (MvPolynomial.map (coefficientEmbedding Omega) quadratic)
            (MvPolynomial.map (coefficientEmbedding Omega) A) (initialCoordinate Omega))=0) ∧
         (ev C=0 ↔ ev (movingCut ((coefficientEmbedding Omega).comp (polynomialEmbedding K)) Q 14
            (MvPolynomial.map (coefficientEmbedding Omega) quadratic)
            (MvPolynomial.map (coefficientEmbedding Omega) A) (initialCoordinate Omega))=0))  := by
  letI : StrongNormalizationMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.strongNormalizationMonoid
  letI : NormalizedGCDMonoid (Polynomial Poly3) := UniqueFactorizationMonoid.toNormalizedGCDMonoid _
  have hj := generic_coefficients_ne_zero K J hJ
  have hq := generic_coefficients_ne_zero K Q hQ
  have hnj := generic_coefficients_degree K J 2 hJdegree
  have hnq := generic_coefficients_degree K Q 14 hQdegree
  have hcop := MovingSourceGenericField6814.generic_coefficients_relPrime K J Q hJ hrel
  obtain ⟨B0,C0,hB0,hC0,hrel0,hBdiv,hCdiv,hzero⟩ := MovingSourceSaturation6814.exists_coprime_cleared_pair
    (coefficients (polynomialEmbedding K) J) (coefficients (polynomialEmbedding K) Q)
    2 14 (2*A) quadratic hj hq hnj hnq hden hcop
  have hjraw := MovingSourceProperness6814.targetPolynomial_ne_zero _ 2 (2*A) quadratic hj hnj hden
  have hqraw := MovingSourceProperness6814.targetPolynomial_ne_zero _ 14 (2*A) quadratic hq hnq hden
  refine ⟨genericTargetMap Omega B0,genericTargetMap Omega C0,?_,?_,
    genericTargetMap_relPrime Omega B0 C0 hB0 hrel0,?_,?_,?_⟩
  · intro hz
    exact hB0 (genericTargetMap_injective Omega (by simpa only [map_zero] using hz))
  · intro hz
    exact hC0 (genericTargetMap_injective Omega (by simpa only [map_zero] using hz))
  · exact normalized_target_flag Omega (polynomialEmbedding K) J 9 U T 2 hJU hUT
      (by omega) hJbounds quadratic A hquadratic hAflag B0 hBdiv hjraw
  · exact normalized_target_flag Omega (polynomialEmbedding K) Q 31 98 1700 14
      (by omega) (by omega) (by omega) hQbounds quadratic A hquadratic hAflag C0 hCdiv hqraw
  · intro L _ ev hev
    have hh := hzero L (ev.comp (genericTargetMap Omega)) (by
      simpa only [RingHom.comp_apply,genericTargetMap_C] using hev)
    change (ev (genericTargetMap Omega B0)=0 ↔ ev (genericTargetMap Omega
        (targetPolynomial (coefficients (polynomialEmbedding K) J) 2 (2*A) quadratic))=0) ∧
      (ev (genericTargetMap Omega C0)=0 ↔ ev (genericTargetMap Omega
        (targetPolynomial (coefficients (polynomialEmbedding K) Q) 14 (2*A) quadratic))=0) at hh
    rw [generic_target_is_movingCut,generic_target_is_movingCut] at hh
    exact hh
end ActualPair
end
end MovingSourceGenericCuts6814
end SubmissionLower
end ProximityPrize
