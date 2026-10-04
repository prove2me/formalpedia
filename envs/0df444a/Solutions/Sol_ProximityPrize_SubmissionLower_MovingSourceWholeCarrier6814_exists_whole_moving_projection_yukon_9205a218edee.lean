-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.exists_whole_moving_projection_yukon_9205a218edee
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T06:32:31.082525+00:00
-- url     : https://prove2.me/submissions/de908802-2f35-483f-b4b1-d5af92a712fb

import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceAutomaticProjection6814_exists_whole_projection_family_yukon_6e73f0a0c288



import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceCarrierZeros6814_movingCut_zero_of_helper_dvd_yukon_9979e66e9721
import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceGenericCuts6814_exists_bounded_generic_pair_yukon_11d063869ac1
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_ccdd8e96359f5f5372a63637
import Definitions.Def_Yukon_9ee250b49ffcc1fbd0a8d65b
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814.exists_whole_projection_family := @ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814.exists_whole_projection_family_yukon_6e73f0a0c288
private abbrev ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814.movingCut_zero_of_helper_dvd := @ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814.movingCut_zero_of_helper_dvd_yukon_9979e66e9721
private abbrev ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.exists_bounded_generic_pair := @ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.exists_bounded_generic_pair_yukon_11d063869ac1
namespace ProximityPrize.SubmissionLower.MovingSourceAutomaticProjection6814
end MovingSourceAutomaticProjection6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
end MovingSourceGeometricBudget6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
end MovingSourceCarrierField6814
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
namespace ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814
end WholeSpaceSourceAlternative6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
end WholeSpaceCubeUniform6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
end WholeSpaceCube6814
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
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
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
namespace ProximityPrize.SubmissionLower.RCN046
end RCN046
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open RCN002 RCN046 RCN095 RCN135 RCN136 RCN207 RCN234 RCN156 RCN264 RCN313 RCN341
open SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceGenericCuts6814 MovingSourceCarrierZeros6814 MovingSourceCarrierField6814
open MovingSourceGeometricBudget6814 MovingSourceAutomaticProjection6814
variable {K : Type} [Field K]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
local notation "lift" => MvPolynomial.map (coefficientEmbedding (GenericField K))
theorem _root_.solution [CharP K 2130706433]
    (J Q : WholeSpaceCube6814.Poly (K:=K))
    (hJ : J≠0) (hQ : Q≠0) (hrel : IsRelPrime J Q)
    (hJdegree : J.degreeOf 1≤2) (hQdegree : Q.degreeOf 1≤14)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hQbounds : ∀ e ∈ Q.support, 2*e 1+e 3≤31 ∧ e 1+e 2+e 3≤98 ∧ e 1+e 2+e 3+e 4≤1700)
    (F : MvPolynomial (Fin 4) K) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hJdiv : F∣helper J F 2 0) (hQdiv : F∣helper Q F 14 0)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A) :
    ∃ base : ∀ C : WholeMovingFamily F quadratic A, SeparableLiteralCoordinate C.1,
      Nonempty (AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩)  := by
  obtain ⟨B,C,hB,hC,hcop,hBflag,hCflag,hzero⟩ := exists_bounded_generic_pair
    J Q hJ hQ hrel hJdegree hQdegree U T (by omega) hUT hJbounds hQbounds
    quadratic A hden hquadratic hA
  have hmem (D : WholeMovingFamily F quadratic A) : B∈D.1 ∧ C∈D.1 := by
    let ev := (coordinateEvaluation OmegaT D.1).toRingHom
    have hR : ev (regularDenominator F A)≠0 := by
      intro hz
      exact regularComponent_H_not_mem OmegaT (wholeCarrier F) (regularEquation F quadratic A)
        (regularDenominator F A) D ((SecondJetComponentRoots.evaluation_zero_iff D.1 _).mp hz)
    have hregular : ev (surfaceMap phi (2*polyH K F))≠0 ∧ ev (lift (2*A))≠0 := by
      simpa only [regularDenominator,map_mul,mul_ne_zero_iff] using hR
    have hF : ev (surfaceMap phi F)=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff D.1 _).mpr
        (regularComponent_G_mem OmegaT (wholeCarrier F) (regularEquation F quadratic A)
          (regularDenominator F A) D)
    have hM : ev (regularEquation F quadratic A)=0 :=
      (SecondJetComponentRoots.evaluation_zero_iff D.1 _).mpr
        (regularComponent_T_mem OmegaT (wholeCarrier F) (regularEquation F quadratic A)
          (regularDenominator F A) D)
    have hJraw := movingCut_zero_of_helper_dvd phi ev J F 2
      (MvPolynomial.degreeOf_le_iff.mp hJdegree) hJdiv hF hregular.1
      (lift quadratic) (lift A) (initialCoordinate Omega) hM
    have hQraw := movingCut_zero_of_helper_dvd phi ev Q F 14
      (MvPolynomial.degreeOf_le_iff.mp hQdegree) hQdiv hF hregular.1
      (lift quadratic) (lift A) (initialCoordinate Omega) hM
    have hz := hzero (CoordinateField OmegaT D.1) ev hregular.2
    exact ⟨(SecondJetComponentRoots.evaluation_zero_iff D.1 B).mp (hz.1.mpr hJraw),
      (SecondJetComponentRoots.evaluation_zero_iff D.1 C).mp (hz.2.mpr hQraw)⟩
  have hc := MovingSourcePrimeFamily6814.source_pair_directional_prices U T hU hUmax hUT hT
  exact exists_whole_projection_family (wholeCarrier F) (regularEquation F quadratic A)
    (regularDenominator F A) B C hB hC hcop (fun D => (hmem D).1) (fun D => (hmem D).2)
    ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩ hBflag hCflag 2130706433
    (hc.1.trans_lt (by decide)) (hc.2.1.trans_lt (by decide))
    (wholeCarrier_derivative_nonzero F hpos hsmall)
end
end MovingSourceWholeCarrier6814
end SubmissionLower
end ProximityPrize
