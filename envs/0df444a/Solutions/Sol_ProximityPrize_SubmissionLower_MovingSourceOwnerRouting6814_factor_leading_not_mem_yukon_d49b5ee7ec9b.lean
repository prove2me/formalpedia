-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814.factor_leading_not_mem_yukon_d49b5ee7ec9b
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T08:33:54.821544+00:00
-- url     : https://prove2.me/submissions/41a59c25-2096-4096-82f2-298099b893b5




import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_8c903be4287ee925ec46b1a5
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
namespace ProximityPrize.SubmissionLower.MovingSourceTwoProfiles6814
end MovingSourceTwoProfiles6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceNativeEnvelope6814
end MovingSourceNativeEnvelope6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerSplit6814
end MovingSourceOwnerSplit6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceNativeFactor6814
end MovingSourceNativeFactor6814
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
namespace ProximityPrize.SubmissionLower.WholeSpaceCubeUniform6814
end WholeSpaceCubeUniform6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.WholeSpaceCube6814
end WholeSpaceCube6814
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
namespace ProximityPrize.SubmissionLower.MovingSourceOwnerRouting6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 500000
open MvPolynomial SecondJetCoefficients SecondJetCarrierDichotomy
open WholeSpaceCube6814 WholeSpaceCubeUniform6814 MovingFiberThreeSources6811
open MovingSourceCarrierField6814 MovingSourceNativeFactor6814 MovingSourceOwnerSplit6814
open MovingSourceNativeEnvelope6814 MovingSourceTwoProfiles6814
open RCN234 RCN156
variable {K : Type} [Field K]
theorem _root_.solution
    {E : Type} [Field E] (phi : Polynomial K →+* E)
    (C : Ideal (MvPolynomial (Fin 3) E))
    (J P : WholeSpaceCube6814.Poly (K:=K)) (hdiv : J∣P)
    (hP : RCN136.surfaceMap phi (asS P).leadingCoeff∉C) :
    RCN136.surfaceMap phi (asS J).leadingCoeff∉C  := by
  intro hJ
  exact hP (C.mem_of_dvd (map_dvd (RCN136.surfaceMap phi) (factor_leading_dvd J P hdiv)) hJ)
end
end MovingSourceOwnerRouting6814
end SubmissionLower
end ProximityPrize
