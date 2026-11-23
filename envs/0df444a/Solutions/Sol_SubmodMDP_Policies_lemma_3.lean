-- Prove2me | solution 1 for SubmodMDP.Policies.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:13:21.524507+00:00
-- url     : https://prove2.me/submissions/760f9811-bf07-4720-8981-8eb4e376f626

import Definitions.Def_SubmodMDP_Policies_Layered

open SubmodMDP.Policies

theorem solution (G : LGraph) (r : ℕ) (hr : 1 ≤ r) (x : Finset (Fin G.N) → ℝ)
    (hx : InQ G r x) (w : Fin G.N) (hw : 0 < x {w}) :
    InQ G (r - 1) (SubmodMDP.Policies.cond x w) := by
  rcases hx with ⟨h1, h2, h3, h4, h5⟩
  have hcard : ∀ I : Finset (Fin G.N), I.card ≤ r - 1 → (insert w I).card ≤ r := by
    intro I hI
    have := Finset.card_insert_le w I
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi1 hi2 u v hu hv harc I hI
    simp only [SubmodMDP.Policies.cond, Finset.insert_comm w]
    rw [← add_div]
    exact div_le_div_of_nonneg_right (h1 i hi1 hi2 u v hu hv harc (insert w I) (hcard I hI)) hw.le
  · intro i hi1 hi2 I hI
    simp only [SubmodMDP.Policies.cond, Finset.insert_comm w, ← Finset.sum_div]
    rw [h2 i hi1 hi2 (insert w I) (hcard I hI)]
  · intro v I hI
    simp only [SubmodMDP.Policies.cond, Finset.insert_comm w]
    exact div_le_div_of_nonneg_right (h3 v (insert w I) (hcard I hI)) hw.le
  · simp [SubmodMDP.Policies.cond, div_self hw.ne']
  · intro I hI
    simp only [SubmodMDP.Policies.cond]
    have hIw : (insert w I).card ≤ r + 1 := by
      have := Finset.card_insert_le w I
      omega
    exact div_nonneg (h5 (insert w I) hIw) hw.le
