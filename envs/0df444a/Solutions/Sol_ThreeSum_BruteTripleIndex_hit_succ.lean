-- Prove2me | solution 1 for ThreeSum.BruteTripleIndex.hit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:07:11.552246+00:00
-- url     : https://prove2.me/submissions/d775f66d-9b3b-4c20-af37-55a965af01d3

import Definitions.Def_Submission_ThreeSum_Coloring
import Definitions.Def_Submission_ThreeSum_BruteTripleIndex

set_option autoImplicit false
open ThreeSum ThreeSum.BruteTripleIndex
namespace ThreeSum.BruteTripleIndex
theorem _root_.solution {n t : ℕ} (x : Fin n → ℤ) (hn : 0 < n) (ht : t < n^3) :
    Hit x hn (t+1) ↔ Hit x hn t ∨ witness x hn ht := by
  constructor
  · rintro ⟨i,hi,hlt,hx⟩
    by_cases he : i=t
    · subst i
      exact Or.inr hx
    · exact Or.inl ⟨i,hi,by omega,hx⟩
  · rintro (⟨i,hi,hlt,hx⟩ | hx)
    · exact ⟨i,hi,by omega,hx⟩
    · exact ⟨t,ht,by omega,hx⟩
end ThreeSum.BruteTripleIndex
