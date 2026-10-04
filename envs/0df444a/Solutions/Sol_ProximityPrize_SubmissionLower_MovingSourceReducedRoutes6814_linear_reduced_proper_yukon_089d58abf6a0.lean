-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceReducedRoutes6814.linear_reduced_proper_yukon_089d58abf6a0
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T23:42:08.93572+00:00
-- url     : https://prove2.me/submissions/c8a20747-83e1-415d-97de-47da93c820fe




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_470e6b3ad95913c90c8c44d8
import Definitions.Def_Yukon_4eb9e7e98149c44e25409e85
import Definitions.Def_Yukon_4f316b5d60b209d4b31c20b9
import Definitions.Def_Yukon_1f886e14a1fc29f50d6a3d3c
import Definitions.Def_Yukon_ca06e00072579899a61b0098
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
theorem _root_.solution
    (F : MvPolynomial (Fin 4) K) [Fact (Irreducible F)]
    (J : WholeSpaceCube6814.Poly (K:=K)) (hdata : LinearRoute F J) (n : ℕ)
    (hproper : ¬F∣RCN313.numerator K F n) :
    ¬F∣numerators (linearH J) (linearG J) n  := by
  intro hnew
  have hn := (carrierMap_zero_iff F _).mpr hnew
  have hc := (carrierMap_zero_iff F _).mpr ((hdata.2.2.2.2 n).1)
  simp only [map_sub,map_mul,map_pow,hn,mul_zero,sub_zero] at hc
  have hz := (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ hdata.2.1)
  exact hproper ((carrierMap_zero_iff F _).mp hz)
end
end MovingSourceReducedRoutes6814
end SubmissionLower
end ProximityPrize
