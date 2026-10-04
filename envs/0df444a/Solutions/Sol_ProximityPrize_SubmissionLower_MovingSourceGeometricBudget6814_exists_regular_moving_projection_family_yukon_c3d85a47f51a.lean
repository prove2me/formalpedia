-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814.exists_regular_moving_projection_family_yukon_c3d85a47f51a
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T02:57:36.816818+00:00
-- url     : https://prove2.me/submissions/47856ca8-b64e-4554-8b17-0f376164fc22

import Definitions.Def_Yukon_b65780c687b1145241867ef4

import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceCarrierZeros6814_movingCut_zero_of_helper_dvd_yukon_9979e66e9721



import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceGenericCuts6814_exists_bounded_generic_pair_yukon_11d063869ac1
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814.movingCut_zero_of_helper_dvd := @ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814.movingCut_zero_of_helper_dvd_yukon_9979e66e9721
private abbrev ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.exists_bounded_generic_pair := @ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.exists_bounded_generic_pair_yukon_11d063869ac1
namespace ProximityPrize.SubmissionLower.MovingSourcePoleBudget6814
end MovingSourcePoleBudget6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
end MovingSourceCarrierZeros6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814
end MovingSourceGenericCuts6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetClearedHelper
end SecondJetClearedHelper
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
end SecondJetCoefficients
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN313
end RCN313
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN264
end RCN264
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN237
end RCN237
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
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open RCN002 RCN095 RCN135 RCN136 RCN207 RCN237 RCN264 RCN313 RCN341
open SecondJetCoefficients SecondJetClearedHelper
open MovingSourceGenericCuts6814 MovingSourceCarrierZeros6814 MovingSourcePoleBudget6814
variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
/-- The final budget is on the original carrier/moving-equation family,
not on a hypothetical family of components of the new cuts. The regular
locus explicitly excludes 2H=0 and 2A=0. -/
theorem _root_.solution
    (J Q : WholeSpaceCube6814.Poly (K := K))
    (hJ : J≠0) (hQ : Q≠0) (hrel : IsRelPrime J Q)
    (hJdegree : J.degreeOf 1≤2) (hQdegree : Q.degreeOf 1≤14)
    (U T : ℕ) (hJU : 9≤U) (hUT : U≤T)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hQbounds : ∀ e ∈ Q.support, 2*e 1+e 3≤31 ∧ e 1+e 2+e 3≤98 ∧ e 1+e 2+e 3+e 4≤1700)
    (F : MvPolynomial (Fin 4) K)
    (hJdiv : F∣helper J F 2 0) (hQdiv : F∣helper Q F 14 0)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic)
    (hA : PolynomialInFlag unitYZFlag A)
    (G : MvPolynomial (Fin 3) OmegaT) (hcarrier : G∣surfaceMap phi F)
    (base : ∀ C : MovingFamily F G quadratic A, SeparableLiteralCoordinate C.1)
    (hY : ∀ C : MovingFamily F G quadratic A, RCN037.LiteralProjectionGate C 0)
    (hZ : ∀ C : MovingFamily F G quadratic A, RCN037.LiteralProjectionGate C 2)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0) :
    Nonempty (RCN046.AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩)  := by
  obtain ⟨B,C,hB,hC,hcop,hBflag,hCflag,hzero⟩ := exists_bounded_generic_pair
    J Q hJ hQ hrel hJdegree hQdegree U T hJU hUT hJbounds hQbounds
    quadratic A hden hquadratic hA
  have hmem (D : MovingFamily F G quadratic A) : B∈D.1 ∧ C∈D.1 := by
    let ev := (coordinateEvaluation OmegaT D.1).toRingHom
    have hR : ev (regularDenominator F A)≠0 := by
      intro hz
      exact regularComponent_H_not_mem OmegaT G (regularEquation F quadratic A)
        (regularDenominator F A) D
        ((SecondJetComponentRoots.evaluation_zero_iff D.1 _).mp hz)
    have hregular : ev (surfaceMap phi (2*polyH K F))≠0 ∧ ev (lift (2*A))≠0 := by
      simpa only [regularDenominator,map_mul,mul_ne_zero_iff] using hR
    have hG : ev G=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff D.1 G).mpr
        (regularComponent_G_mem OmegaT G (regularEquation F quadratic A) (regularDenominator F A) D)
    have hF : ev (surfaceMap phi F)=0 := by
      have hh := map_dvd ev hcarrier
      rwa [hG,zero_dvd_iff] at hh
    have hM : ev (regularEquation F quadratic A)=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff D.1 _).mpr
        (regularComponent_T_mem OmegaT G (regularEquation F quadratic A) (regularDenominator F A) D)
    have hJraw := movingCut_zero_of_helper_dvd phi ev J F 2
      (MvPolynomial.degreeOf_le_iff.mp hJdegree) hJdiv hF hregular.1
      (lift quadratic) (lift A) (initialCoordinate Omega) hM
    have hQraw := movingCut_zero_of_helper_dvd phi ev Q F 14
      (MvPolynomial.degreeOf_le_iff.mp hQdegree) hQdiv hF hregular.1
      (lift quadratic) (lift A) (initialCoordinate Omega) hM
    have hz := hzero (CoordinateField OmegaT D.1) ev hregular.2
    exact ⟨(SecondJetComponentRoots.evaluation_zero_iff D.1 B).mp (hz.1.mpr hJraw),
      (SecondJetComponentRoots.evaluation_zero_iff D.1 C).mp (hz.2.mpr hQraw)⟩
  obtain ⟨D⟩ := RCN037.exists_adaptiveNestedProjectionData base hY hZ hderiv
  exact ⟨projectionFamily_of_coprime_pair base hY hZ hderiv D B C hB hC hcop
    (fun E => (hmem E).1) (fun E => (hmem E).2)
    ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ hBflag hCflag⟩
end
end MovingSourceGeometricBudget6814
end SubmissionLower
end ProximityPrize
