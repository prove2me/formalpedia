-- Prove2me | solution 2 for StudentTeacher976.Adaptivity.adaptivity_separation_of_total_search_selectors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T11:30:20.077394+00:00
-- url     : https://prove2.me/submissions/75ac379e-635e-4476-8b4d-d0397649622d

import Theorems.Thm_StudentTeacher976_Adaptivity_presented_adaptivity_separation
import Theorems.Thm_StudentTeacher976_Adaptivity_uniform_refutation_translation_transfer
import Theorems.Thm_StudentTeacher976_Adaptivity_refutation_translation_of_selectors
set_option autoImplicit false
open StudentTeacher976.Adaptivity

theorem solution (i : ℕ) (hardness : ¬ StudentTeacher976.Adaptivity.Sigma (i+1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q)
    (hselectors : SelectorPresentationTranslation.SelectorCollapse i) :
    ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q := by
  obtain ⟨R,P,⟨f,hf,hs,hw⟩,hno⟩ := presented_adaptivity_separation i hardness r q hr hq
  intro hinc
  obtain ⟨Q,g,hg,hshape,hwin⟩ := hinc ⟨P,f,hf,hs,hw⟩
  obtain ⟨ψ,heff,hlen,htest⟩ := refutation_translation_of_selectors i hselectors R P Q
  obtain ⟨g',hg',hs',hw'⟩ := uniform_refutation_translation_transfer P Q r q hq.1 ψ heff hlen htest g hg hshape hwin
  exact hno ⟨g',hg',hs',hw'⟩
