-- Prove2me | solution 1 for ThreeSum.WeightedGlobalTensorWordResources.kernel_guard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:11:10.209228+00:00
-- url     : https://prove2.me/submissions/1b376af7-e6f8-438b-96fc-886d814c807a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_Submission_Weighted_Global_TernaryTensorWordResources
import Theorems.Thm_ThreeSum_WeightedGlobalTensorWordResources_potential_word_bound

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J count V sourceU : ℕ) :
    LightTernaryPairedPotential.word K (J+2) V≤(word K J count V sourceU : ℤ) := by
  apply (potential_word_bound K J V).trans
  exact_mod_cast (show potentialWord K J V≤word K J count V sourceU by unfold word; omega)
end ThreeSum.WeightedGlobalTensorWordResources
