-- Prove2me | solution 1 for SZ.quadPisot_mem_S_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T20:59:51.025226+00:00
-- url     : https://prove2.me/submissions/4da8263e-67db-48ae-af0e-41428fdbe021

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Classification
import Theorems.Thm_SZ_quadPisot_mem_MahlerZ
import Theorems.Thm_SZ_golden_mem_S


set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution {α : ℝ} (h : IsQuadPisot α) : α ∈ S ↔ α = golden := by
  constructor
  · intro hS
    by_contra hne
    exact hS.2 (quadPisot_mem_MahlerZ h hne)
  · rintro rfl; exact golden_mem_S
end SZ
