-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceGenericCuts6814.normalized_target_flag_yukon_8a92d1b35601
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T01:19:45.1233+00:00
-- url     : https://prove2.me/submissions/f41fe6c4-a5e6-434a-a449-c7c573beaff4

import Definitions.Def_Yukon_6db579f0800634a21a2958ad



import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
import Definitions.Def_Yukon_cab3e47590aea7a2fd8756f8
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
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
/-- Gcd-normalized cuts inherit the same flags after the generic target
extension, by divisibility; no additional degree cost is charged. -/
theorem _root_.solution {K : Type*} [Field K]
    (phi : Polynomial K →+* E) (P : WholeSpaceCube6814.Poly (K := K))
    (B U T s : ℕ) (hBU : B ≤ U) (hUT : U ≤ T) (hsB : 2*s ≤ B)
    (hP : ∀ e ∈ P.support, 2*e 1+e 3 ≤ B ∧ e 1+e 2+e 3 ≤ U ∧ e 1+e 2+e 3+e 4 ≤ T)
    (quadratic A : MvPolynomial (Fin 3) E)
    (hQ : PolynomialInFlag (2 • unitAllFlag) quadratic) (hA : PolynomialInFlag unitYZFlag A)
    (V : Polynomial (MvPolynomial (Fin 3) E))
    (hdiv : V ∣ targetPolynomial (coefficients phi P) s (2*A) quadratic)
    (hne : targetPolynomial (coefficients phi P) s (2*A) quadratic≠0) :
    PolynomialInFlag ⟨T-U,U-B+s,B⟩ (genericTargetMap E V)  := by
  apply flag_of_dvd (GenericField E) _ _ _ (map_dvd (genericTargetMap E) hdiv)
  · intro hz
    exact hne (genericTargetMap_injective E (by simpa only [map_zero] using hz))
  · exact generic_target_flag E phi P B U T s hBU hUT hsB hP quadratic A hQ hA
end
end MovingSourceGenericCuts6814
end SubmissionLower
end ProximityPrize
