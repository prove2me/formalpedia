-- Prove2me | solution 1 for PoWMining.CostStatics.eq_B5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T07:34:07.606289+00:00
-- url     : https://prove2.me/submissions/ee3604b7-22ba-481d-aa8f-90295c10e0ef

import Mathlib
import Definitions.Def_PoWMining_CostStatics_Setting
set_option autoImplicit false
open PoWMining.CostStatics

theorem solution {n : ℕ} (c : Fin n → ℝ) (γ R : ℝ) (hS : Standing c γ R) (i : Fin n) :
    R * ((c i + γ * gH c γ R) / (R + γ * gH c γ R ^ 2)) = c i + γ * hstar c γ R i := by
  have hR := hS.R_pos
  have hγ := hS.γ_nonneg
  have hd : R + γ * gH c γ R ^ 2 ≠ 0 := by positivity
  unfold hstar fH
  field_simp
  ring
