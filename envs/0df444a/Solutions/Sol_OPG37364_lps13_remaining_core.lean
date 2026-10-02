-- Prove2me | solution 1 for OPG37364.lps13_remaining_core
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-09-12T14:14:37.518659+00:00
-- url     : https://prove2.me/submissions/61c975af-9ade-4e30-b2c0-f30153052a11

import Theorems.Thm_OPG37364_lps13Graph_connected_of_large
import Theorems.Thm_OPG37364_lps13Graph_hasGirthAtLeast_of_pow_lt_sq
import Theorems.Thm_OPG37364_lps13_adjacency_spectrum_lt_twelve_of_large

set_option autoImplicit false
open scoped Classical

namespace OPG37364

theorem _root_.solution :
    ∀ g : ℕ, 3 ≤ g →
      ∃ B : ℕ, ∀ (q : ℕ) [Fact q.Prime] (hq : 13 < q) (i : LPS13Root q),
        B < q → legendreSym q 13 = -1 →
        letI : Fintype (Matrix.ProjGenLinGroup (Fin 2) (ZMod q)) := Fintype.ofFinite _
        IsConnected (lps13Graph hq i) ∧ HasGirthAtLeast (lps13Graph hq i) g ∧
          (∀ μ : ℝ, μ ∈ spectrum ℝ ((lps13Graph hq i).adjMatrix ℝ) →
            μ ≠ 14 → μ < 12) := by
  intro g _
  obtain ⟨Bspec, hspec⟩ := lps13_adjacency_spectrum_lt_twelve_of_large
  refine ⟨max (13^60) (max (13^g) Bspec), ?_⟩
  intro q hp hq i hB hnr
  have hc : 13^60 < q := lt_of_le_of_lt (le_max_left _ _) hB
  have hg : 13^g < q := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hB
  have hs : Bspec < q := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hB
  refine ⟨lps13Graph_connected_of_large hc i hnr, ?_, hspec hq hs i hnr⟩
  apply lps13Graph_hasGirthAtLeast_of_pow_lt_sq hq i g
  have hsq : q ≤ q^2 := by nlinarith
  omega

end OPG37364
