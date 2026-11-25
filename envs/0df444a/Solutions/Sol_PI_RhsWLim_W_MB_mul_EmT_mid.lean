-- Prove2me | solution 1 for PI.RhsWLim.W.MB.mul_EmT_mid
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:13:56.303614+00:00
-- url     : https://prove2.me/submissions/efa5b1e3-0f43-49a3-baca-6be546cc79a6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
import Theorems.Thm_PI_RhsWLim_W_MB_wI_midx
import Theorems.Thm_PI_RhsWLim_W_MB_wI_inj

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
theorem _root_.solution {X : Type*} [Fintype X] (A : Matrix X (Fin (k + 1)) ℂ) (j : Fin (2 * r + k + 1)) (x : X) (hj : mid k r j) :
    (A * (Em k r)ᵀ) x j = A x (midx hj) := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (midx hj)]
  · rw [Matrix.transpose_apply, Em, if_pos (wI_midx hj).symm, mul_one]
  · intro b _ hb
    rw [Matrix.transpose_apply, Em, if_neg, mul_zero]
    intro h
    apply hb
    apply wI_inj (r := r)
    rw [wI_midx hj, h]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.RhsWLim.W.MB
