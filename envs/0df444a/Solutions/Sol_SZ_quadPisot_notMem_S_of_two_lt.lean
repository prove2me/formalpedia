-- Prove2me | solution 1 for SZ.quadPisot_notMem_S_of_two_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:01:29.60745+00:00
-- url     : https://prove2.me/submissions/cf87bc03-e753-425f-9917-2fbbeda01159

import Definitions.Def_SZ_Silver
import Definitions.Def_SZ_Tijdeman
import Definitions.Def_SZ_QuadThm6
import Definitions.Def_SZ_GoldenS
import Mathlib.Tactic.LinearCombination
import Definitions.Def_SZ_Classification
import Theorems.Thm_SZ_quadPisot_mem_S_iff

set_option autoImplicit false
open SZ
open Real
namespace SZ
theorem _root_.solution {α : ℝ} (h : IsQuadPisot α) (hα : 2 < α) :
    α ∉ S := by
  intro hS
  have hsq : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hpos : 0 < Real.sqrt 5 := Real.sqrt_pos.mpr (by norm_num)
  have h5 : Real.sqrt 5 < 3 := by nlinarith
  have he := (quadPisot_mem_S_iff h).mp hS
  rw [he, golden] at hα
  linarith
end SZ
