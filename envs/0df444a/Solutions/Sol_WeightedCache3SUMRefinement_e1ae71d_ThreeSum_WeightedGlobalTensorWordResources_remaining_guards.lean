-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources.remaining_guards
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:00:15.327722+00:00
-- url     : https://prove2.me/submissions/5838dece-21b7-4d1d-9643-eeb2f2d63cf7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_LightTernaryTensorFactoryReady
import Definitions.Def_Submission_ThreeSum_PolynomialResources
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryTensorWordResources

set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
open LightTernaryPairedPolynomial TernaryPairedColumnEnumeration StageBounds
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
theorem _root_.solution (K J count V sourceU : ℕ) :
    (sourceU+1)^2≤word K J count V sourceU ∧
    J+3≤word K J count V sourceU ∧ count≤word K J count V sourceU ∧
    (J+2)^4≤word K J count V sourceU ∧
    LightWeightRow.word 4 (J+2) ((J+2)^4) 0 1≤word K J count V sourceU := by
  unfold word
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalTensorWordResources
