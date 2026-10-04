-- Prove2me | solution 1 for ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814.exists_regular_coprime_target_cuts_yukon_7be3d510497f
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-10-03T01:01:18.917218+00:00
-- url     : https://prove2.me/submissions/61adc875-9418-4e10-bd45-d51d0e13aeae

import Definitions.Def_Yukon_10805ee98000946934f31f50

import Definitions.Def_Yukon_6d3add3a3f6938cc0bdd10e2



import Definitions.Def_Yukon_196ff1de7425c8d8df8d3a11
import Definitions.Def_Yukon_867f9fe91b5fcd4219c71561
import Definitions.Def_Yukon_91e99a7c9682f8cc19028ba7
import Definitions.Def_Yukon_6db579f0800634a21a2958ad
import Definitions.Def_Yukon_ca06e00072579899a61b0098
set_option backward.isDefEq.respectTransparency.types false
namespace ProximityPrize.SubmissionLower.MovingSourceSaturation6814
end MovingSourceSaturation6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceGenericField6814
end MovingSourceGenericField6814
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.MovingSourceClearing6814
end MovingSourceClearing6814
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
namespace ProximityPrize.SubmissionLower.RCN136
end RCN136
end SubmissionLower
end ProximityPrize
namespace ProximityPrize.SubmissionLower.RCN135
end RCN135
end SubmissionLower
end ProximityPrize
namespace MvPolynomial
end MvPolynomial
namespace ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
open MvPolynomial RCN135 RCN136 SecondJetCoefficients SecondJetClearedHelper
open MovingSourceClearing6814 MovingSourceGenericField6814 MovingSourceSaturation6814
variable (K : Type*) [Field K]
local notation "Omega" => GenericField K
local notation "Poly3" => MvPolynomial (Fin 3) Omega
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814.instStrongNormalizationMonoidPolynomialMvPolynomialFinOfNatNatGenericField
attribute [local instance] _root_.ProximityPrize.SubmissionLower.MovingSourceCoprimeCuts6814.instNormalizedGCDMonoidPolynomialMvPolynomialFinOfNatNatGenericField
/-- The two returned cuts are nonzero and coprime before moving-target
specialization. On the regular denominator locus their zeros agree with
the actual cleared source equations, uniformly in every field evaluation.
No post-clearing properness or zero-set equivalence is a premise. -/
theorem _root_.solution
    (J Q : WholeSpaceCube6814.Poly (K := K))
    (hJ : J≠0) (hQ : Q≠0) (hrel : IsRelPrime J Q)
    (hJdegree : J.degreeOf 1 ≤ 2) (hQdegree : Q.degreeOf 1 ≤ 14)
    (quadratic A : Poly3) (hA : (2 : Poly3)*A≠0) :
    ∃ U V : Polynomial Poly3, U≠0 ∧ V≠0 ∧ IsRelPrime U V ∧
      U ∣ targetPolynomial (coefficients (polynomialEmbedding K) J) 2 (2*A) quadratic ∧
      V ∣ targetPolynomial (coefficients (polynomialEmbedding K) Q) 14 (2*A) quadratic ∧
      ∀ (L : Type*) [Field L] (ev : Poly3 →+* L) (target : L), ev (2*A)≠0 →
        ((Polynomial.eval₂ ev target U=0 ↔
          cleared ((coefficients (polynomialEmbedding K) J).map ev) 2 (ev (2*A))
            (target-ev quadratic)=0) ∧
         (Polynomial.eval₂ ev target V=0 ↔
          cleared ((coefficients (polynomialEmbedding K) Q).map ev) 14 (ev (2*A))
            (target-ev quadratic)=0))  := by
  obtain ⟨U,V,hU,hV,hcop,hUdiv,hVdiv,hzero⟩ := exists_coprime_cleared_pair
    (coefficients (polynomialEmbedding K) J) (coefficients (polynomialEmbedding K) Q)
    2 14 (2*A) quadratic (generic_coefficients_ne_zero K J hJ)
    (generic_coefficients_ne_zero K Q hQ) (generic_coefficients_degree K J 2 hJdegree)
    (generic_coefficients_degree K Q 14 hQdegree) hA (generic_coefficients_relPrime K J Q hJ hrel)
  refine ⟨U,V,hU,hV,hcop,hUdiv,hVdiv,?_⟩
  intro L _ ev target hden
  have hz := hzero L (Polynomial.eval₂RingHom ev target) (by simpa using hden)
  change (Polynomial.eval₂ ev target U=0 ↔ Polynomial.eval₂ ev target
      (targetPolynomial (coefficients (polynomialEmbedding K) J) 2 (2*A) quadratic)=0) ∧
    (Polynomial.eval₂ ev target V=0 ↔ Polynomial.eval₂ ev target
      (targetPolynomial (coefficients (polynomialEmbedding K) Q) 14 (2*A) quadratic)=0) at hz
  rw [eval_targetPolynomial,eval_targetPolynomial] at hz
  exact hz
end
end MovingSourceCoprimeCuts6814
end SubmissionLower
end ProximityPrize
