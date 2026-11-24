-- Prove2me | solution 1 for TightContinualCounting.LowerBounds.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T13:47:53.96988+00:00
-- url     : https://prove2.me/submissions/1480e507-2533-4608-9ed5-f8cce3f7a119

import Mathlib
import Definitions.Def_TightContinualCounting_LowerBounds_probes

open TightContinualCounting.LowerBounds

theorem solution {d : ℕ} (v : Fin d → ℝ) (u u' : Finset (Fin d))
    (hu' : u'.Nonempty) (hsub : u' ⊆ u) :
    |midProbe u' v - midProbe u v| ≤ (rangePotential u v - rangePotential u' v) / 2 := by
  have hu : u.Nonempty := hu'.mono hsub
  have h1 : coordinateMax u' v ≤ coordinateMax u v := by
    simp only [coordinateMax, dif_pos hu, dif_pos hu']
    exact Finset.sup'_le hu' v (fun i hi => Finset.le_sup' v (hsub hi))
  have h2 : coordinateMin u v ≤ coordinateMin u' v := by
    simp only [coordinateMin, dif_pos hu, dif_pos hu']
    exact Finset.le_inf' hu' v (fun i hi => Finset.inf'_le v (hsub hi))
  simp only [midProbe, rangePotential]
  rw [abs_le]
  constructor <;> linarith
