-- Prove2me | solution 3 for StudentTeacher976.Adaptivity.adaptivity_separation_of_advice_total_search_selectors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:44:11.473143+00:00
-- url     : https://prove2.me/submissions/9582aaab-4346-4f71-b857-82d63b11bb6a

import Theorems.Thm_StudentTeacher976_Adaptivity_presented_adaptivity_separation_with_advice
import Theorems.Thm_StudentTeacher976_Adaptivity_presentation_transfer_with_advice_iff_total_search_selectors
set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (hardness : ¬StudentTeacher976.Adaptivity.Sigma (i+1)⊆DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hselectors : AdviceSelectorTranslation.SelectorCollapse i) :
    ¬ST i (fun m => r m+1) (fun _ => 1)⊆ST i r q := by
  have hinvariance := (presentation_transfer_with_advice_iff_total_search_selectors i r q hr hq).mpr hselectors
  obtain ⟨R,P,⟨f,hf,hs,hw⟩,hno⟩ := presented_adaptivity_separation_with_advice i hardness r q hr hq
  intro hinc
  obtain ⟨Q,g,hg,hshape,hwin⟩ := hinc ⟨P,f,hf,hs,hw⟩
  exact hno (hinvariance R P Q ⟨g,hg,hshape,hwin⟩)
