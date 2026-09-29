-- Prove2me | solution 1 for WeinbergLeptons.eq7_massTerm
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T01:23:24.885464+00:00
-- url     : https://prove2.me/submissions/64d989c7-c63a-4f9e-bead-f1a28eb20bb4

import Mathlib
import Definitions.Def_WeinbergLeptons_Model

set_option autoImplicit false

open WeinbergLeptons Matrix in
theorem solution (g g' lam : ℝ) (V : Fin 4 → ℝ) :
    vectorMassTerm g g' lam V = -(1 / 2) * (V ⬝ᵥ (massSqMatrix g g' lam *ᵥ V)) := by
  simp [vectorMassTerm, massSqMatrix, mulVec, dotProduct, Fin.sum_univ_four]
  ring
