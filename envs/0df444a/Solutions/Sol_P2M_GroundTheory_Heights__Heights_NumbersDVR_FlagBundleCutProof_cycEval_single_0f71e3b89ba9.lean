-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleCutProof_cycEval_single_0f71e3b89ba9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:06:42.276397+00:00
-- url     : https://prove2.me/submissions/ddbfb62c-6780-4437-8552-6ac1399c4386

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleForms
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleSectionDiv
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PIntNumSymm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleCut

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof
theorem _root_.solution {K : Type} {ι : K → Type} {F : Type} [Field F]
    (n : Ideal (MRing ι F) → ℤ) (Z : Ideal (MRing ι F)) :
    cycEval n (fun W => by classical exact if W = Z then 1 else 0) = n Z := by
  classical
  unfold cycEval
  rw [finsum_eq_single _ Z (fun W hW => by simp [hW])]
  simp
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleCutProof
