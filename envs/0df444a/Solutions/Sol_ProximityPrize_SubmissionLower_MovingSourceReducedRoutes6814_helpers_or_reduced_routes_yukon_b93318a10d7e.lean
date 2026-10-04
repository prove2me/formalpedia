-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceReducedRoutes6814.helpers_or_reduced_routes_yukon_b93318a10d7e
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T23:40:55.030042+00:00
-- url     : https://prove2.me/submissions/8f3d4c51-ed89-4522-991a-0c13eb8059f6




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_ef32f3d6934bd47f231d0d68
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
import Definitions.Def_Yukon_8c903be4287ee925ec46b1a5
import Definitions.Def_Yukon_4a0b8ca13aa8ab32899f444d
import Definitions.Def_Yukon_1f886e14a1fc29f50d6a3d3c
import Definitions.Def_Yukon_8b73aecc71f3e1b6f34fc101
import Definitions.Def_Yukon_5f00e2c5310c2b2de34fe4e2
import Definitions.Def_Yukon_a98065d48a835a5fe7279317
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLinearOwnerData6814
end MovingSourceLinearOwnerData6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceFlowNumerator6814
end MovingSourceFlowNumerator6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceLinearFlow6814
end MovingSourceLinearFlow6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceNativeFactor6814
end MovingSourceNativeFactor6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
end MovingSourceOwnerRouting6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814
end MovingSourceOwnerSplit6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
end MovingSourceTwoProfiles6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
end MovingSourceCarrierField6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingFiberThreeSources6811
end MovingFiberThreeSources6811
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetCarrierDichotomy
end SecondJetCarrierDichotomy
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.SecondJetCoefficients
end SecondJetCoefficients
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceReducedRoutes6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 300000
open MvPolynomial SecondJetCoefficients SecondJetCarrierDichotomy
open MovingFiberThreeSources6811 MovingSourceCarrierField6814 MovingSourceTwoProfiles6814
open MovingSourceOwnerSplit6814 MovingSourceOwnerRouting6814 MovingSourceNativeFactor6814
open MovingSourceLinearFlow6814 MovingSourceFlowNumerator6814 MovingSourceLinearOwnerData6814
open RCN234 RCN156
variable {K : Type} [Field K]
theorem _root_.solution [CharP K 2130706433]
    {N : Type} [Fintype N] (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 3429<wt residualTotalWeights F) (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t) :
    (∃ Q, WholeSpaceSourceAlternative6814.ProperHelper F Q r y t nodes u0 u1) ∨
    (∃ Q, MovingSourceZSupplier6814.ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ S : Source F, ∃ Sz : Source F,
      Profile S 31 98 995 14 2 3 ∧ Profile Sz 53 177 3429 24 6 8 ∧
      ∃ J, Irreducible J ∧ J∣S.P ∧ rootEvaluation (carrierMap F) (ratio (carrierMap F) F) J=0 ∧
        (LinearRoute F J ∨ NativeRoute F J ∨
          ∃ D, Irreducible D ∧ (D∣S.P ∨ D∣Sz.P) ∧
            rootEvaluation (carrierMap F) (ratio (carrierMap F) F) D=0 ∧ IsRelPrime J D)  := by
  rcases helpers_or_two_profiles nodes u0 u1 hN F Fact.out hFT r y t hr hy ht hF with
    hhelp | hhelp | ⟨S,Sz,hS,hZ⟩
  · exact Or.inl hhelp
  · exact Or.inr (Or.inl hhelp)
  · exact Or.inr (Or.inr ⟨S,Sz,hS,hZ,retained_reduced_routes F S Sz hS hZ hFT hpos hsmall⟩)
end
end MovingSourceReducedRoutes6814
end SubmissionLower
end ProximityPrize
