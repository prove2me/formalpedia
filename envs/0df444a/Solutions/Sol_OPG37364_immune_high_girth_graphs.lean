-- Prove2me | solution 1 for OPG37364.immune_high_girth_graphs
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T09:04:45.651089+00:00
-- url     : https://prove2.me/submissions/e8d5eaeb-da03-459d-b0d8-baafc3cf7d3b

import Theorems.Thm_OPG37364_exists_high_girth_strict_cut_expander
import Theorems.Thm_OPG37364_not_hasMatchingCut_of_smallCut_expansion
import Theorems.Thm_OPG37364_regular_bipartite_hasPerfectMatching

set_option autoImplicit false

open OPG37364

theorem solution :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsImmuneHighGirthPackage G g := by
  intro g hg
  obtain ⟨n, hn, G, hconn, hbip, hreg, hgirth, hexp⟩ :=
    exists_high_girth_strict_cut_expander g hg
  exact ⟨n, hn, G, hconn, hbip, hreg, hgirth,
    not_hasMatchingCut_of_smallCut_expansion hexp,
    regular_bipartite_hasPerfectMatching G 14 (by decide) hreg hbip⟩
