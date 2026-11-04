-- Prove2me | solution 1 for ThreeSum.ColorScan.hit_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:37:55.317819+00:00
-- url     : https://prove2.me/submissions/bd7d7625-ccd9-4f58-af9f-0f7ab333323c

import Definitions.Def_Submission_ThreeSum_ColorParameters
import Definitions.Def_Submission_ThreeSum_ColorScan

set_option autoImplicit false
open ThreeSum ThreeSum.ColorScan
open ColorParameters
namespace ThreeSum.ColorScan
theorem _root_.solution {n W t : ℕ} (x : Fin n → ℤ) (ht : t < count W) :
    Hit x W (t+1) ↔ Hit x W t ∨ ColorClassLists.witness (parameter ht) x := by
  constructor
  · rintro ⟨i,hi,hlt,hx⟩
    by_cases he : i=t
    · subst i
      exact Or.inr hx
    · exact Or.inl ⟨i,hi,by omega,hx⟩
  · rintro (⟨i,hi,hlt,hx⟩ | hx)
    · exact ⟨i,hi,by omega,hx⟩
    · exact ⟨t,ht,by omega,hx⟩
end ThreeSum.ColorScan
