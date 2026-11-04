-- Prove2me | solution 1 for ThreeSum.LightSpanRowEqual.prefix_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:23.190668+00:00
-- url     : https://prove2.me/submissions/0f299e9b-c137-4269-a2b7-7d7a37d3d642

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanRowEqual
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
namespace ThreeSum.LightSpanRowEqual
theorem _root_.solution (f g : ℕ → ℤ) (j : ℕ) :
    (∀ i<j+1, f i=g i) ↔ (∀ i<j, f i=g i) ∧ f j=g j := by
  constructor
  · intro h; exact ⟨fun i hi => h i (by omega),h j (by omega)⟩
  · rintro ⟨h,he⟩ i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
    · exact h i hi
    · exact he
end ThreeSum.LightSpanRowEqual
