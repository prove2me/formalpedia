-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTensorWordResources.remaining_guards
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:44:10.614194+00:00
-- url     : https://prove2.me/submissions/761032bc-0d7e-4e66-8749-561d54c02803

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J count V sourceU : ℕ) :
    (sourceU+1)^2≤word K J count V sourceU ∧
    J+3≤word K J count V sourceU ∧ count≤word K J count V sourceU ∧
    (J+2)^4≤word K J count V sourceU ∧
    LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1≤word K J count V sourceU := by
  unfold word
  omega
end ThreeSum.WeightedGlobalTensorWordResources
