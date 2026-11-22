-- Prove2me | solution 1 for TreeEquivalenceHORS.Equivalence.theorem_1_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-21T19:11:46.964722+00:00
-- url     : https://prove2.me/submissions/96a13953-aed3-47b8-8887-da5cd03ee891

import Theorems.Thm_TreeEquivalenceHORS_Equivalence_lemma_6_2
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_tree_equivalence_tests_of_exact_prefixes
import Theorems.Thm_TreeEquivalenceHORS_Equivalence_four_tree_equivalence_languages_undecidable

namespace TreeEquivalenceHORS.Equivalence
private theorem coCE_of_tests {P : ℕ → Prop} (test : ℕ → ℕ → Bool)
    (hc : Computable₂ test) (hs : ∀ n, P n ↔ ∀ d, test n d = true) : CoCE P := by
  have search := (Partrec.rfind (p := fun n d => Part.some (!(test n d)))
    (Primrec.not.to_comp.comp hc).partrec.to₂).dom_re
  apply search.of_eq
  intro n
  rw [Nat.rfind_dom (p := fun d => Part.some (!(test n d))), hs]
  simp

private theorem proved_here
    (pf : ∃ f : ℕ × ℕ × ℕ → ℕ, Computable f ∧
      ∀ (G : HORS) (t : Tm) (d : ℕ), G.Valid → G.typeOf [] t = some .o →
        f (Encodable.encode G, Encodable.encode t, d) = Encodable.encode (G.Pref t d)) :
    (CoCEComplete EqHORS ∧ ¬ ComputablePred EqHORS) ∧
    (CoCEComplete Eq4Sigma2 ∧ ¬ ComputablePred Eq4Sigma2) ∧
    (CoCEComplete Eq4Sigma2Prod ∧ ¬ ComputablePred Eq4Sigma2Prod) ∧
    (CoCEComplete Eq4Sigma2SafeProd ∧ ¬ ComputablePred Eq4Sigma2SafeProd) := by
  have tests := tree_equivalence_tests_of_exact_prefixes pf
  have result (P) (hp : P ∈ [EqHORS, Eq4Sigma2, Eq4Sigma2Prod, Eq4Sigma2SafeProd]) :
      CoCEComplete P ∧ ¬ ComputablePred P := by
    obtain ⟨test, c, eq⟩ := tests P hp
    obtain ⟨hard, undec⟩ := four_tree_equivalence_languages_undecidable P hp
    exact ⟨⟨coCE_of_tests test c eq,hard⟩,undec⟩
  exact ⟨result _ (by simp),result _ (by simp),result _ (by simp),result _ (by simp)⟩


end TreeEquivalenceHORS.Equivalence
open TreeEquivalenceHORS.Equivalence

theorem solution :
    (CoCEComplete EqHORS ∧ ¬ ComputablePred EqHORS) ∧
    (CoCEComplete Eq4Sigma2 ∧ ¬ ComputablePred Eq4Sigma2) ∧
    (CoCEComplete Eq4Sigma2Prod ∧ ¬ ComputablePred Eq4Sigma2Prod) ∧
    (CoCEComplete Eq4Sigma2SafeProd ∧ ¬ ComputablePred Eq4Sigma2SafeProd) := proved_here lemma_6_2.2
