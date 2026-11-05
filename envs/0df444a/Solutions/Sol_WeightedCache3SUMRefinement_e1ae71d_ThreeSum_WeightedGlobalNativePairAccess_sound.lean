-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T12:31:44.817839+00:00
-- url     : https://prove2.me/submissions/f6178714-b844-4a83-a9bc-f1a545ee092f

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryCompactPairedSupport
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_Global_TernaryNativePairAccess
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCompactPairedSupport_native_left_lt
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedGlobalCompactPairedSupport_native_right_lt


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
noncomputable section
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess
theorem _root_.solution {N : ℕ} (S : WeightedSourceCountExecutionFactory.Setup N)
    (A B C : ℕ→ℤ) (position : ℕ→ℕ) (nA : ℕ)
    (hpos : ∀ i<S.front.count, position i<nA) :
    (∃ i<S.front.count, ∃ p : Pair S i, mode B C p=A (position i)) →
    ∃ i<nA, ∃ j<S.left.NL, ∃ k<S.right.NL, C k=A i+B j := by
  rintro ⟨i,hi,p,hp⟩
  refine ⟨position i,hpos i hi,p.val.1.1,
    WeightedGlobalCompactPairedSupport.native_left_lt p,p.val.2.1,
    WeightedGlobalCompactPairedSupport.native_right_lt p,?_⟩
  unfold mode at hp
  omega
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalNativePairAccess
