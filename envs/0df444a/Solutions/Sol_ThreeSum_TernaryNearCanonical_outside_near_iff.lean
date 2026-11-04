-- Prove2me | solution 1 for ThreeSum.TernaryNearCanonical.outside_near_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:44.3692+00:00
-- url     : https://prove2.me/submissions/991c0c5c-6223-4ced-be29-ecd43b52e403

import Definitions.Def_Submission_ThreeSum_TernaryNearBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Definitions.Def_Submission_ThreeSum_LightTernaryNearPair
import Definitions.Def_Submission_ThreeSum_TernaryNearCanonical
import Theorems.Thm_ThreeSum_TernaryBank_mem_nearWords
import Theorems.Thm_ThreeSum_TernaryBank_rank_add_deficit
attribute [local simp] ThreeSum.TernaryBank.mem_nearWords



set_option autoImplicit false
open ThreeSum ThreeSum.TernaryNearCanonical
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryBankEnumeration
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace ThreeSum.TernaryNearCanonical
theorem _root_.solution {N : ℕ} (Q R : TritWord N) (T : ℕ) (hQ : T<rank Q) :
    R∈nearWords Q (rank Q-(T+1)) ↔ Below R Q ∧ T<rank R := by
  rw [mem_nearWords]
  constructor
  · intro ⟨hbelow,hdef⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩
  · intro ⟨hbelow,hrank⟩
    have hsum := rank_add_deficit hbelow
    exact ⟨hbelow,by omega⟩
end ThreeSum.TernaryNearCanonical
