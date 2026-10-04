-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.helper_or_whole_projection_yukon_30585f547133
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T07:13:19.523779+00:00
-- url     : https://prove2.me/submissions/f682c784-d943-44e7-8cd6-d2ea716b0a27




import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceCarrierField6814_exists_helper_or_global_pair_yukon_fb7f70c232a5
import Theorems.Thm_ProximityPrize_SubmissionLower_MovingSourceWholeCarrier6814_exists_whole_moving_projection_yukon_9205a218edee
import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_07bb1fdf83fc478e7c5449e7
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
import Definitions.Def_Yukon_32972018b92a668e7c3a547c
import Definitions.Def_Yukon_9ee250b49ffcc1fbd0a8d65b
import Definitions.Def_Yukon_ca06e00072579899a61b0098
import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
import Definitions.Def_Yukon_a98065d48a835a5fe7279317
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.MovingSourceCarrierField6814.exists_helper_or_global_pair := @ProximityPrize.SubmissionLower.MovingSourceCarrierField6814.exists_helper_or_global_pair_yukon_fb7f70c232a5
private abbrev ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.exists_whole_moving_projection := @ProximityPrize.SubmissionLower.MovingSourceWholeCarrier6814.exists_whole_moving_projection_yukon_9205a218edee
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
/-- Actual source selection and the shared WHOLE-carrier budget. No
irreducible geometric carrier or per-geometric-factor price is an input. -/
theorem _root_.solution [CharP K 2130706433]
    {N : Type} [Fintype N] (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K:=K)) (hJi : Irreducible J)
    (hmid : 25≤MvPolynomial.weightedTotalDegree middleWeights J)
    (hB : MvPolynomial.weightedTotalDegree slopeWeights J=9) (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hU : 25≤U) (hUmax : U≤30) (hUT : U≤T) (hT : T≤331)
    (hJbounds : ∀ e ∈ J.support, 2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)] (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1)
    (quadratic A : MvPolynomial (Fin 3) Omega) (hden : (2 : MvPolynomial (Fin 3) Omega)*A≠0)
    (hquadratic : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
      ∃ base : ∀ C : WholeMovingFamily F quadratic A, SeparableLiteralCoordinate C.1,
        Nonempty (AdaptiveUnitProjectionFamily base ⟨T-U,U-9+2,9⟩ ⟨1602,81,31⟩)  := by
  rcases exists_helper_or_global_pair nodes u0 u1 hN J hJi hmid hB hJdegree U T hJbounds
    (by omega) F hFT r y t hr hy ht hF hpos hsmall hroot with hhelp | hpair
  · exact Or.inl hhelp
  obtain ⟨Q,hQ,hcop,hJdiv,hQdiv,hQbounds,hQdegree⟩ := hpair
  exact Or.inr (exists_whole_moving_projection J Q hJi.ne_zero hQ hcop hJdegree hQdegree
    U T hU hUmax hUT hT hJbounds hQbounds F hpos hsmall hJdiv hQdiv
    quadratic A hden hquadratic hA)
end
end MovingSourceWholeCarrier6814
end SubmissionLower
end ProximityPrize
