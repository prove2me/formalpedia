-- Prove2me | solution 1 for SZ.gVal_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:12:39.380001+00:00
-- url     : https://prove2.me/submissions/52f704e8-f517-4ac7-bf01-fd601cda061d

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_SZ_valS_stepS
import Theorems.Thm_SZ_gState_succ
import Theorems.Thm_SZ_pick_residual_mem


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {s : ℤ × ℤ} (h : GStart s) (k : ℕ) :
    0 ≤ valS (gState s k) ∧ valS (gState s k) ≤ 3 + 3 * Real.sqrt 3 := by
  induction k with
  | zero => exact ⟨h.1, h.2.1⟩
  | succ k ih =>
    obtain ⟨hlo, hhi⟩ := pick_residual_mem ih.1 ih.2
    have key : valS (gState s (k + 1)) = 3 * (valS (gState s k)
        - (((pick (valS (gState s k))).1 : ℝ)
            + ((pick (valS (gState s k))).2 : ℝ) * Real.sqrt 3)) := by
      rw [gState_succ, valS_stepS]; rfl
    rw [key]
    constructor <;> linarith
end SZ
