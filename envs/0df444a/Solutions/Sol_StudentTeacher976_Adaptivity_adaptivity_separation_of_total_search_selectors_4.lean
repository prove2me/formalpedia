-- Prove2me | solution 4 for StudentTeacher976.Adaptivity.adaptivity_separation_of_total_search_selectors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T13:29:44.391137+00:00
-- url     : https://prove2.me/submissions/3528a383-a603-4026-b9c6-236db83d4f5e

import Theorems.Thm_StudentTeacher976_Adaptivity_presented_adaptivity_separation
import Theorems.Thm_StudentTeacher976_Adaptivity_presentation_invariance_iff_total_search_selectors
set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (hardness : ¬ StudentTeacher976.Adaptivity.Sigma (i+1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hselectors : SelectorPresentationTranslation.SelectorCollapse i) :
    ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q := by
  have hinvariance := (presentation_invariance_iff_total_search_selectors i r q hr hq).mpr hselectors
  obtain ⟨R,P,⟨f,hf,hs,hw⟩,hno⟩ := presented_adaptivity_separation i hardness r q hr hq
  intro hinc
  obtain ⟨Q,g,hg,hshape,hwin⟩ := hinc ⟨P,f,hf,hs,hw⟩
  exact hno (hinvariance R P Q ⟨g,hg,hshape,hwin⟩)
