-- Prove2me | solution 1 for ThirdLawThermo.adiabatic_unattainability
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T10:12:00.536595+00:00
-- url     : https://prove2.me/submissions/b8503063-ae20-43a0-9014-801aee776b1f

import Definitions.Def_ThirdLawThermo_Defs
import Mathlib

open Filter Topology
open ThirdLawThermo

theorem solution {X : Type*} (S : ℝ → X → ℝ)
    (hmono : ∀ x : X, StrictMonoOn (fun T => S T x) (Set.Ici 0))
    (hNernst : ∀ x y : X, S 0 x = S 0 y)
    (T : ℝ) (x : X) (T' : ℝ) (x' : X) (hT : 0 < T) (hT' : 0 ≤ T')
    (hS : S T' x' = S T x) :
    T' ≠ 0 := by
  rintro rfl
  have h := hmono x (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hT.le) hT
  simp only at h
  rw [← hS, hNernst x' x] at h
  exact lt_irrefl _ h
