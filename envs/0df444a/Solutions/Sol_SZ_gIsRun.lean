-- Prove2me | solution 1 for SZ.gIsRun
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:16:12.969876+00:00
-- url     : https://prove2.me/submissions/8f0bec4b-7ace-45a7-ae0f-83e8298c5103

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_evenDigit_pick
import Theorems.Thm_SZ_gVal_mem
import Theorems.Thm_SZ_runState_gDigit
import Theorems.Thm_SZ_pick_residual_mem


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s : ℤ × ℤ} (h : GStart s) : IsRun s (gDigit s) := by
  intro k
  rw [runState_gDigit]
  obtain ⟨hlo, hhi⟩ := pick_residual_mem (gVal_mem h k).1 (gVal_mem h k).2
  exact ⟨evenDigit_pick _, hlo, hhi⟩
end SZ
