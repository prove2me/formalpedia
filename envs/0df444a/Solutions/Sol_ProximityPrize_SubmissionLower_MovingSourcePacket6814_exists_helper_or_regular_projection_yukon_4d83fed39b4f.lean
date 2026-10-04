-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourcePacket6814.exists_helper_or_regular_projection_yukon_4d83fed39b4f
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T04:12:59.658512+00:00
-- url     : https://prove2.me/submissions/2c84b051-2e59-439f-96c2-f94379b1de74

import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceCarrierField6814_exists_helper_or_global_pair_yukon_fb7f70c232a5
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8



import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceGeometricBudget6814_exists_regular_moving_projection_family_yukon_c3d85a47f51a
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_ba2ee1ab868a502d09acf5a7
import Definitions.Def_Yukon_ca06e00072579899a61b0098
import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
import Definitions.Def_Yukon_a98065d48a835a5fe7279317
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceCarrierField6814.exists_helper_or_global_pair := @ProximityPrize.SubmissionLower.MovingSourceCarrierField6814.exists_helper_or_global_pair_yukon_fb7f70c232a5
private abbrev ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814.exists_regular_moving_projection_family := @ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814.exists_regular_moving_projection_family_yukon_c3d85a47f51a
namespace ProximityPrize.SubmissionLower.MovingSourceGeometricBudget6814
end MovingSourceGeometricBudget6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
end MovingSourceCarrierField6814
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
namespace ProximityPrize.SubmissionLower.RCN341
end RCN341
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
namespace ProximityPrize.SubmissionLower.RCN084
end RCN084
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN046
end RCN046
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN042
end RCN042
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN037
end RCN037
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN003
end RCN003
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN002
end RCN002
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourcePacket6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2500000
open MvPolynomial RCN002 RCN003 RCN037 RCN042 RCN046 RCN084 RCN095 RCN135 RCN136 RCN234 RCN156 RCN264 RCN341
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierField6814 MovingSourceGeometricBudget6814
variable {K N : Type} [Field K] [CharP K 2130706433] [Fintype N]
local notation "Omega" => GenericField K
local notation "OmegaT" => GenericField (GenericField K)
local notation "phi" => RingHom.comp (coefficientEmbedding (GenericField K)) (polynomialEmbedding K)
/-- No desired count, source dimension, faithful map, helper identity, or
projection-data supplier is assumed. This is the regular simple-quadratic
branch; its ownership/coverage hypotheses remain visible. -/
theorem _root_.solution
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hJU : 9≤U) (hUT : U≤T) (hT : T≤1700)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((SecondJetCoefficients.asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (G : MvPolynomial (Fin 3) OmegaT) (hcarrier : G∣surfaceMap phi F)
    (hG : Irreducible G) (hproper : ¬G∣regularEquation F quadratic A)
    (hderiv : MvPolynomial.pderiv (1 : Fin 3) G≠0)
    (p q : FlagDegree) (hp : PolynomialInFlag p G)
    (hq : PolynomialInFlag q (regularEquation F quadratic A))
    (hdeg : p.zOnly+p.yz+p.all<2130706433)
    (hmix : 2*(p.zOnly+p.yz+p.all)*(q.zOnly+q.yz+q.all)<2130706433) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ base : ∀ C : MovingFamily F G quadratic A, SeparableLiteralCoordinate C.1,
        Nonempty (AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩)  := by
  rcases exists_helper_or_global_pair nodes u0 u1 hN J hJi hmid hB hJdegree U T hJbounds hT
    F hFT r y t hr hy ht hF hpos hsmall hroot with hhelp | hpair
  · exact Or.inl hhelp
  obtain ⟨Q,hQ,hcop,hJdiv,hQdiv,hQbounds,hQdegree⟩ := hpair
  obtain ⟨base,hY,hZ⟩ := exists_projection_data G (regularEquation F quadratic A)
    (regularDenominator F A) hG hproper p q hp hq 2130706433 hdeg hmix
  exact Or.inr ⟨base,exists_regular_moving_projection_family J Q hJi.ne_zero hQ hcop
    hJdegree hQdegree U T hJU hUT hJbounds hQbounds F hJdiv hQdiv
    quadratic A hden hquadratic hA G hcarrier base hY hZ hderiv⟩
end
end MovingSourcePacket6814
end SubmissionLower
end ProximityPrize
