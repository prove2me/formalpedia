-- Prove2me | solution 1 for SZ.digitReal_le_digitSum_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:01:40.017168+00:00
-- url     : https://prove2.me/submissions/282a338f-f842-45f8-896b-4bcc83d90e87

import Definitions.Def_SZ_SqrtThree
import Mathlib.Algebra.AlgebraicCard
import Mathlib.SetTheory.Cardinal.Continuum
import Definitions.Def_SZ_CoverTree
import Theorems.Thm_P2M_SZ_IsDigits_pow_pos__7f25d03f067c
import Theorems.Thm_SZ_digitSum_le_of_le
import Theorems.Thm_SZ_digitSum_monotone


set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution {m : ℕ} {d : ℕ → ℤ} (h : IsDigits m d) (k : ℕ) :
    digitReal m d ≤ digitSum m d k + 1 / (m : ℝ) ^ k := by
  refine ciSup_le fun j => ?_
  rcases le_or_gt k j with hj | hj
  · have hb := digitSum_le_of_le h hj
    have hp : (0:ℝ) < 1 / (m : ℝ) ^ j := one_div_pos.mpr (h.pow_pos' j)
    linarith
  · have hb := digitSum_monotone h hj.le
    have hp : (0:ℝ) < 1 / (m : ℝ) ^ k := one_div_pos.mpr (h.pow_pos' k)
    linarith
end SZ
