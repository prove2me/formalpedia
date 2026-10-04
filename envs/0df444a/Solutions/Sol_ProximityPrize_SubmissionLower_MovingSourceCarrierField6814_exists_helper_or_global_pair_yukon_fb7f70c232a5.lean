-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceCarrierField6814.exists_helper_or_global_pair_yukon_fb7f70c232a5
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T03:32:44.584401+00:00
-- url     : https://prove2.me/submissions/03fe5a2b-b619-490c-8405-8944bc7ad582


import Theorems.Thm_ProximityPrize_SubmissionLower_WholeSpaceSourceAlternative6814_exists_helper_or_curvature_pair_yukon_41fc34ab79ed
import Definitions.Def_Yukon_a98065d48a835a5fe7279317



import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
import Definitions.Def_Yukon_6031b066ec5b1f25736844be
import Definitions.Def_Yukon_ca06e00072579899a61b0098
import Definitions.Def_Yukon_9e6b0bff61d8a97ca7ca80a3
set_option backward.isDefEq.respectTransparency.types false
private abbrev ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814.exists_helper_or_curvature_pair := @ProximityPrize.SubmissionLower.WholeSpaceSourceAlternative6814.exists_helper_or_curvature_pair_yukon_41fc34ab79ed
namespace ProximityPrize.SubmissionLower.RCN156
end RCN156
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN234
end RCN234
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierZeros6814
end MovingSourceCarrierZeros6814
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
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceCarrierField6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial SecondJetCoefficients SecondJetClearedHelper
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 WholeSpaceSourceAlternative6814
open MovingSourceCarrierZeros6814 RCN234 RCN156
variable {K : Type} [Field K]
/-- Received-word data and the actual simple-quadratic branch yield both
global carrier identities. Neither a faithful-map assumption nor either
helper-divisibility conclusion is a premise. -/
theorem _root_.solution
    {N : Type} [Fintype N] [CharP K 2130706433]
    (nodes : N ↪ K) (u0 u1 : N → K) (hN : Fintype.card N=262144)
    (J : WholeSpaceCube6814.Poly (K := K)) (hJi : Irreducible J)
    (hmid : 25≤weightedTotalDegree middleWeights J)
    (hB : weightedTotalDegree slopeWeights J=9)
    (hJdegree : J.degreeOf 1≤2)
    (U T : ℕ) (hJbounds : ∀ e ∈ J.support,
      2*e 1+e 3≤9 ∧ e 1+e 2+e 3≤U ∧ e 1+e 2+e 3+e 4≤T)
    (hT : T≤1700)
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (hFT : 1700<wt residualTotalWeights F)
    (r y t : ℕ) (hr : 1≤r) (hy : 1≤y) (ht : 1≤t)
    (hF : wt residualSWeights F≤r ∧ wt residualYSWeights F≤y ∧ wt residualTotalWeights F≤t)
    (hpos : 0<F.degreeOf 2) (hsmall : F.degreeOf 2<2130706433)
    (hroot : ((asS J).map (carrierMap F)).rootMultiplicity
      (SecondJetCarrierDichotomy.ratio (carrierMap F) F)=1) :
    (∃ Q, ProperHelper F Q r y t nodes u0 u1) ∨
    ∃ Q : WholeSpaceCube6814.Poly (K := K), Q≠0 ∧ IsRelPrime J Q ∧
      F∣helper J F 2 0 ∧ F∣helper Q F 14 0 ∧
      (∀ e ∈ Q.support, 2*e 1+e 3≤31 ∧ e 1+e 2+e 3≤98 ∧ e 1+e 2+e 3+e 4≤1700) ∧
      Q.degreeOf 1≤14  := by
  have hH := carrier_H_nonzero F hpos hsmall
  have hJne := carrier_polynomial_nonzero F J hJi.ne_zero T
    (fun e he => (hJbounds e he).2.2) (hT.trans_lt hFT)
  rcases exists_helper_or_curvature_pair nodes u0 u1 hN J hJi hmid hB F Fact.out
    hFT r y t hr hy ht hF (carrierMap F) (carrierMap_self F) hH hJne hroot with hhelp | hp
  · exact Or.inl hhelp
  obtain ⟨Q,hQ,hcop,hzero,hTotal,hMid,hSlope,hDegree⟩ := hp
  right
  refine ⟨Q,hQ,hcop,?_,?_,?_,hDegree⟩
  · exact helper_dvd_of_generic_root J F (carrierMap F) (carrierMap_zero_iff F) 2
      (MvPolynomial.degreeOf_le_iff.mp hJdegree) hH (simple_root_vanishes _ _ hroot)
  · exact helper_dvd_of_generic_root Q F (carrierMap F) (carrierMap_zero_iff F) 14
      (MvPolynomial.degreeOf_le_iff.mp hDegree) hH hzero
  · intro e he
    have hs := (MvPolynomial.le_weightedTotalDegree slopeWeights he).trans hSlope
    have hm := (MvPolynomial.le_weightedTotalDegree middleWeights he).trans hMid
    have ht := (MvPolynomial.le_weightedTotalDegree totalWeights he).trans hTotal
    exact ⟨by simpa [weight_coords,slopeWeights,Nat.mul_comm] using hs,
      by simpa [weight_coords,middleWeights] using hm,
      by simpa [weight_coords,totalWeights] using ht⟩
end
end MovingSourceCarrierField6814
end SubmissionLower
end ProximityPrize
