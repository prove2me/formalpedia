-- Prove2me | solution 1 for ThreeSum.LightIrreducibleFinder.degreePrefix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:40:36.752552+00:00
-- url     : https://prove2.me/submissions/3a61069c-12c6-47d5-9853-f394b11bf86c

import Definitions.Def_Submission_ThreeSum_LightExtensionFactorSearch
import Definitions.Def_Submission_ThreeSum_LightArgumentTable
import Definitions.Def_Submission_ThreeSum_TernaryExtensionSearchCorrect
import Definitions.Def_Submission_ThreeSum_TernaryCoefficientCodes
import Definitions.Def_Submission_ThreeSum_LightTernaryRowSelector
import Definitions.Def_Submission_ThreeSum_LightIrreducibleFinder

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
namespace ThreeSum.LightIrreducibleFinder
theorem _root_.solution (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) :
    (∀ t<j+1, factorFirst C q f (t+1)=0) ↔
      (∀ t<j, factorFirst C q f (t+1)=0) ∧ factorFirst C q f (j+1)=0 := by
  constructor
  · intro h; exact ⟨fun t ht => h t (by omega),h j (by omega)⟩
  · rintro ⟨h,he⟩ t ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · exact h t ht
    · exact he
end ThreeSum.LightIrreducibleFinder
