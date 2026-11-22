-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.lemma_6_2
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:44:45.560721+00:00
-- url     : https://prove2.me/submissions/f3252a5b-4b43-47dc-8857-f95a1a3c04f3

import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_6_1
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_exact_read_of_head_adequacy
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_exact_prefix_algorithm

open TreeEquivalenceHORS.Equivalence

theorem solution :
    (∀ G : HORS, G.Valid → ∀ t : Tm, G.typeOf [] t = some .o →
      ∀ w : List ℕ, G.read t w = Part.some (G.BTat t w)) ∧
    ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d) := by
  exact ⟨fun G vg t ht w => exact_read_of_head_adequacy vg (lemma_6_1 G vg) t ht w,exact_prefix_algorithm⟩

