-- Prove2me | solution 1 for OPG37364.exists_high_girth_strict_cut_expander
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-09T09:56:17.043261+00:00
-- url     : https://prove2.me/submissions/65e675cb-1473-4912-89df-94ab02e7cb93

import Theorems.Thm_OPG37364_exists_high_girth_spectral_expander
import Theorems.Thm_OPG37364_smallCut_expansion_of_spectralGap_gt_one_seventh

set_option autoImplicit false
open scoped Classical
open OPG37364

theorem solution :
    ∀ g : ℕ, 3 ≤ g →
      ∃ n : ℕ, 2 ≤ n ∧ ∃ G : SimpleGraph (Fin n),
        IsConnected G ∧ IsBipartite G ∧ IsRegularOfDegree G 14 ∧
        HasGirthAtLeast G g ∧
        (∀ S : Set (Fin n), S.Nonempty → Sᶜ.Nonempty →
          S.encard ≤ Sᶜ.encard → S.encard < (cutPairs G S).encard) := by
  intro g hg
  obtain ⟨n, hn, G, hconn, hbip, hreg, hgirth, hgap⟩ := exists_high_girth_spectral_expander g hg
  exact ⟨n, hn, G, hconn, hbip, hreg, hgirth,
    smallCut_expansion_of_spectralGap_gt_one_seventh hn G hconn hreg hgap⟩
