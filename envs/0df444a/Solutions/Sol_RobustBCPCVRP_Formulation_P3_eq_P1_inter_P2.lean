-- Prove2me | solution 1 for RobustBCPCVRP.Formulation.P3_eq_P1_inter_P2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:20:04.202443+00:00
-- url     : https://prove2.me/submissions/3000d5c4-d21f-46c4-ae8d-eb0b30c63df7

import Mathlib
import Definitions.Def_LysgaardCVRP_Shrink_cut
import Definitions.Def_LysgaardCVRP_Shrink_roundedCapacityBound
import Definitions.Def_RobustBCPCVRP_Formulation_Setting
import Definitions.Def_RobustBCPCVRP_Formulation_Polytopes
set_option autoImplicit false
open LysgaardCVRP.Shrink RobustBCPCVRP.Formulation

theorem solution {n : ℕ} (E : Finset (Sym2 (Fin (n + 1))))
    (d : Fin (n + 1) → ℕ) (K C : ℕ) (x : Sym2 (Fin (n + 1)) → ℝ) :
    InP3 E d K C x ↔ InP1 E d K C x ∧ InP2 E d K C x := by
  unfold InP3 InP1 InP2
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨h1, h6, h2, h7⟩⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5, h6⟩, ⟨-, -, -, h7⟩⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
