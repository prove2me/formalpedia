-- Prove2me | solution 1 for OPG37364.exists_high_girth_spectral_expander
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T10:49:16.071857+00:00
-- url     : https://prove2.me/submissions/fc94a8a2-0ac5-4d32-9545-ead2c41bb865

import Theorems.Thm_OPG37364_exists_high_girth_adjacency_expander
import Theorems.Thm_OPG37364_spectralGap_gt_one_seventh_of_adjacency_bound

set_option autoImplicit false
open scoped Classical
open OPG37364

theorem solution :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
        HasGirthAtLeast G g ∧
        (1 : ℝ) / 7 < MarkovMixing.spectralGap (MarkovMixing.graphWalk G) := by
  intro g hg
  obtain ⟨n, hn, G, hconn, hbip, hreg, hgirth, hAdj⟩ := exists_high_girth_adjacency_expander g hg
  exact ⟨n, hn, G, hconn, hbip, hreg, hgirth,
    spectralGap_gt_one_seventh_of_adjacency_bound G hconn hreg hAdj⟩
