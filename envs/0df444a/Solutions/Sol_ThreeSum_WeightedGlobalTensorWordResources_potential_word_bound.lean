-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTensorWordResources.potential_word_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:01:39.328575+00:00
-- url     : https://prove2.me/submissions/e7f8c8cf-4384-4ba6-9dee-e3f38898f3e4

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_ThreeSum_WeightedGlobalTensorWordResources_polynomial_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J V : ℕ) :
    LightTernaryPairedPotential.word K (J+2) V≤(potentialWord K J V : ℤ) := by
  have hp := polynomial_bound K V
  unfold LightTernaryPairedPotential.word potentialWord
  push_cast
  gcongr
end ThreeSum.WeightedGlobalTensorWordResources
