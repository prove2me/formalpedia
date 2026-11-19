-- Prove2me | solution 2 for StudentTeacher976.Adaptivity.adaptivity_separation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T09:32:27.684195+00:00
-- url     : https://prove2.me/submissions/97d69bb5-337b-45bd-b48a-c6e446b9aec9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_StudentTeacher976_Adaptivity_adaptivity_separation_of_total_search_selectors
import Theorems.Thm_StudentTeacher976_Adaptivity_adaptivity_separation_of_hard_total_search
set_option autoImplicit false
open QAdvFew.PoQOracle StudentTeacher976.Adaptivity

theorem solution (i : ℕ)
    (hardness : ¬ StudentTeacher976.Adaptivity.Sigma (i+1) ⊆ DeltaPoly i)
    (r q : ℕ → ℕ) (hr : AdmissibleRounds r) (hq : AdmissibleQueries q) :
    ¬ ST i (fun m => r m+1) (fun _ => 1) ⊆ ST i r q := by
  classical
  by_cases hs : SelectorPresentationTranslation.SelectorCollapse i
  · exact adaptivity_separation_of_total_search_selectors i hardness r q hr hq hs
  · have hex : ∃ T : SearchRelation,
        {s | ∃ x y,s=tup [x,y] ∧ T x y}∈Delta i ∧
        (∀ x,∃ y,T x y) ∧
        ∃ b : Polynomial ℕ,(∀ x y,T x y → y.length≤b.eval x.length) ∧
        ¬ ∃ F : Word → Word,InFP i F ∧ ∀ x,T x (F x) := by
      by_contra hn
      apply hs
      intro T hT ht b hb
      by_contra hno
      exact hn ⟨T,hT,ht,b,hb,hno⟩
    obtain ⟨T,hT,ht,b,hb,hno⟩ := hex
    exact adaptivity_separation_of_hard_total_search i hardness T hT ht b hb hno r q hr hq
