-- Prove2me | solution 1 for OPG37364.opg_negative_corollary
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-08T21:16:42.663229+00:00
-- url     : https://prove2.me/submissions/dbc8b2d3-212f-4348-9340-06b5f25cf822

import Theorems.Thm_OPG37364_immune_high_girth_graphs
import Definitions.Def_opg37364_matching_cuts

theorem solution :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        OPG37364.IsConnected G ∧ OPG37364.IsRegularOfDegree G 14 ∧
        OPG37364.HasGirthAtLeast G g ∧ ¬ OPG37364.HasMatchingCut G := by
  intro g hg
  obtain ⟨n, hn, G, hconn, -, hreg, hgirth, hcut, -⟩ :=
    OPG37364.immune_high_girth_graphs g hg
  exact ⟨n, hn, G, hconn, hreg, hgirth, hcut⟩
