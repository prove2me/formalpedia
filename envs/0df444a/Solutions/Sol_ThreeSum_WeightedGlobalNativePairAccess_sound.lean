-- Prove2me | solution 1 for ThreeSum.WeightedGlobalNativePairAccess.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T16:03:35.492086+00:00
-- url     : https://prove2.me/submissions/d9422abc-f224-4833-b023-6a5ce5ce206a

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryCanonicalNativeCompleteness
import Definitions.Def_Submission_Weighted_Global_TernaryCompactPairedSupport
import Definitions.Def_Submission_Weighted_Global_TernaryNativePairAccess
import Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_native_left_lt
import Theorems.Thm_ThreeSum_WeightedGlobalCompactPairedSupport_native_right_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalNativePairAccess
open Finset TernaryJointType WeightedGlobalNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000
namespace ThreeSum.WeightedGlobalNativePairAccess
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
end ThreeSum.WeightedGlobalNativePairAccess
