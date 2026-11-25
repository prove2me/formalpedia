-- Prove2me | solution 1 for PI.Residue.real_hit_ineq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:13.263647+00:00
-- url     : https://prove2.me/submissions/754d0695-29cd-4c12-95ba-21a616721b62

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnitPreserving
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_RealHitIneq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical
noncomputable section
open PI PI.Residue
namespace PI.Residue
theorem _root_.solution (A N s : ℝ) (hA : 0 < A) (hN : 0 < N) (hs : 1 < s) (h : N ≤ 2 * A) :
    A / N ≤ A * (2 * A) ^ (s - 1) * N ^ (-s) := by
  have hP : 0 < N ^ (s - 1) := Real.rpow_pos_of_pos hN _
  have hPB : N ^ (s - 1) ≤ (2 * A) ^ (s - 1) := Real.rpow_le_rpow hN.le h (by linarith)
  have hNs : N ^ s = N ^ (s - 1) * N := by
    rw [← Real.rpow_add_one hN.ne']; ring_nf
  rw [Real.rpow_neg hN.le, hNs]
  have e : A * (2 * A) ^ (s - 1) * (N ^ (s - 1) * N)⁻¹ = A / N * ((2 * A) ^ (s - 1) / N ^ (s - 1)) := by
    field_simp
  rw [e]
  exact le_mul_of_one_le_right (by positivity) ((one_le_div hP).2 hPB)
end PI.Residue
