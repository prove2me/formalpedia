-- Prove2me | solution 1 for ThreeSum.LightSpanCatalogTest.present_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:24.244598+00:00
-- url     : https://prove2.me/submissions/d90c579a-82ef-46e8-83bb-82568771f4f2

import Definitions.Def_Submission_ThreeSum_LightSpanCatalogStep
import Definitions.Def_Submission_ThreeSum_TernaryOriginalSpanCatalog
import Definitions.Def_Submission_ThreeSum_LightSpanCatalogTest

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightSpanCatalogTest
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
namespace ThreeSum.LightSpanCatalogTest
theorem _root_.solution (f : ℕ → ℕ → ℤ) (row : ℕ → ℤ) (J n : ℕ) :
    Present f row J (n+1) ↔ Present f row J n ∨ ∀ i<J, f n i=row i := by
  constructor
  · rintro ⟨k,hk,he⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact Or.inl ⟨k,hk,he⟩
    · exact Or.inr he
  · rintro (⟨k,hk,he⟩ | he)
    · exact ⟨k,by omega,he⟩
    · exact ⟨n,by omega,he⟩
end ThreeSum.LightSpanCatalogTest
