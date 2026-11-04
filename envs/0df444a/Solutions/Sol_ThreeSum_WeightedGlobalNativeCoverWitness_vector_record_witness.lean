-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativeCoverWitness.vector_record_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:33:21.903205+00:00
-- url     : https://prove2.me/submissions/e2dd1f5a-de4f-4a7f-862f-332a682672a7

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryOversizePrime
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryOriginalKeyCodes
import Definitions.Def_Submission_Weighted_Global_TernaryNativeCoverWitness
import Theorems.Thm_ThreeSum_WeightedGlobalNativeCoverWitness_local_record_witness

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativeCoverWitness
open Finset TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters
open WeightedGlobalCoverGoodMaps WeightedGlobalCoverFrequency TernaryFixedDictionaries
open TernaryCanonicalDictionaries
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option maxHeartbeats 3000000
namespace ThreeSum.WeightedGlobalNativeCoverWitness
theorem _root_.solution (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, Covers m p B τ (maps i) (a,b))
    {r : ℕ} (a b : Fin r → ZMod p) :
    ∃ occurrence : Fin r → I, ∃ edge : Fin r → ActualEdge m,
      ∀ j, maps (occurrence j)∉rawBadMaps m p τ ∧
        leftRecord (occurrence j) (edge j)∈records false maps B ∧
        rightRecord (occurrence j) (edge j)∈records true maps B ∧
        leftNative maps (leftRecord (occurrence j) (edge j))=a j ∧
        rightNative maps (rightRecord (occurrence j) (edge j))=b j ∧
        outputHash (maps (occurrence j)) (output (edge j))=a j+b j := by
  classical
  have hh (j : Fin r) := local_record_witness maps B τ hcover (a j) (b j)
  choose occurrence edge he using hh
  exact ⟨occurrence,edge,he⟩
end ThreeSum.WeightedGlobalNativeCoverWitness
