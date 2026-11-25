-- Prove2me | solution 1 for PI.RhsWLim.W.MB.emb_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:30:01.794986+00:00
-- url     : https://prove2.me/submissions/1cfa1a30-337e-4892-9d96-09ea3e269f15

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_emb_eq
import Theorems.Thm_PI_RhsWLim_W_MB_Q_Em
import Theorems.Thm_PI_RhsWLim_W_MB_sandwich

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
theorem _root_.solution (a b : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) : embWb k r (a * b) = embWb k r a * embWb k r b := by
  have h := sandwich (r := r) a b 1 1 (by rw [Matrix.one_mul, Matrix.mul_one]) (by rw [Matrix.one_mul, Matrix.mul_one])
  rw [Matrix.mul_one] at h
  rw [h, emb_eq, Matrix.mul_one, Matrix.mul_one]
  congr 1
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Q_Em, Matrix.zero_mul, sub_zero]
end PI.RhsWLim.W.MB
