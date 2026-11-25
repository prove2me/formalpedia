-- Prove2me | solution 1 for PI.RhsWLim.W.MB.EmT_Em
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:37:23.489454+00:00
-- url     : https://prove2.me/submissions/09d19ced-33b5-4b9e-8b3c-088a824f46af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_RhsWLim
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_VolumeLieE
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeightedLimitGauge_MBaseMem
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
theorem _root_.solution : (Em k r)ᵀ * Em k r = 1 := by
  ext a b
  rw [Matrix.mul_apply, Finset.sum_eq_single (wI k r a)]
  · simp only [Matrix.transpose_apply, Em, if_true, Matrix.one_apply]
    by_cases hab : a = b
    · subst hab; simp
    · rw [if_neg (fun h => hab (wI_inj h)), if_neg hab, mul_zero]
  · intro i _ hi
    simp only [Matrix.transpose_apply, Em]
    rw [if_neg hi (c := i = wI k r a), zero_mul]
  · intro h; exact absurd (Finset.mem_univ _) h
end PI.RhsWLim.W.MB
