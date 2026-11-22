-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_6_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:26:23.065192+00:00
-- url     : https://prove2.me/submissions/1f22771c-175d-4b76-bb56-fc7473821b2b

import Theorems.Thm_TreeEquivalenceHORS_Equivalence_positive_finite_denotation_converges
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_head_convergence_has_positive_denotation

open TreeEquivalenceHORS.Equivalence

theorem solution (G : HORS) (hG : G.Valid) (t : Tm) (ht : G.typeOf [] t = some .o) :
    G.den [] G.etaStar [] t = .bit true ↔ ∃ (c : ℕ) (us : List Tm), G.HeadConv t c us := by
  exact ⟨positive_finite_denotation_converges G hG t ht,head_convergence_has_positive_denotation G hG t ht⟩

