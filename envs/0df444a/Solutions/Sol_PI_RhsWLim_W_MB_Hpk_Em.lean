-- Prove2me | solution 1 for PI.RhsWLim.W.MB.Hpk_Em
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:55:35.804947+00:00
-- url     : https://prove2.me/submissions/b7dac964-972b-4e97-8ee0-71211aac4e78

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_Em_mul_mid
import Theorems.Thm_PI_RhsWLim_W_MB_Em_mul_out

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Matrix
open scoped ENNReal
open PI PI.RhsWLim PI.RhsWLim.W PI.RhsWLim.W.MB
open PI.RhsWLim
variable {k r : ℕ}
namespace PI.RhsWLim.W.MB
theorem _root_.solution : Hpk k r * Em k r = Em k r * Hb k := by
  ext i m
  have h1 : (Hpk k r * Em k r) i m = Hpk k r i (wI k r m) := by
    rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r m)]
    · rw [Em, if_pos rfl, mul_one]
    · intro b _ hb
      rw [Em, if_neg hb, mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [h1]
  have hm := m.isLt
  have hil := i.isLt
  by_cases hi : mid k r i
  · rw [Em_mul_mid _ i _ hi]
    have h0 := hi
    unfold Hpk Hb
    rw [Matrix.diagonal_apply]
    simp only [wI, midx, Fin.ext_iff, Fin.val_last]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rw [Em_mul_out _ i _ hi]
    unfold Hpk
    simp only [wI, Fin.ext_iff]
    split_ifs <;> first | rfl | (exfalso; omega)
end PI.RhsWLim.W.MB
