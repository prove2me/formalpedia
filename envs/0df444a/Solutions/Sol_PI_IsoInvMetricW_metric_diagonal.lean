-- Prove2me | solution 1 for PI.IsoInvMetricW.metric_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:52.369434+00:00
-- url     : https://prove2.me/submissions/da17793a-7fd8-40ae-83de-67af2e0c69a7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_ColChoiceFintype
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Theorems.Thm_PI_IsoInvMetricW_oe_eq_of_range_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical
open PI PI.IsoInvMetricW
open PI.IsoInvMetric
namespace PI.IsoInvMetricW
theorem _root_.solution : EDiag := by
  intro Lt _ _ N nu d I J
  unfold E
  split_ifs with hIJ
  · subst hIJ
    refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
    have : (Matrix.of fun i k : Fin ((nu s).colLen c) =>
        Matrix.diagonal (d s) (I s c i) (I s c k)) = Matrix.diagonal (fun i => d s (I s c i)) := by
      ext i k
      simp [Matrix.diagonal_apply, (I s c).injective.eq_iff]
    rw [this, Matrix.det_diagonal]
  · have : ∃ s c, I s c ≠ J s c := by
      by_contra hne
      push_neg at hne
      exact hIJ (funext fun s => funext fun c => hne s c)
    obtain ⟨s, c, hsc⟩ := this
    have : ∃ i, ∀ k, J s c k ≠ I s c i := by
      by_contra hne
      push_neg at hne
      exact hsc (oe_eq_of_range_sub _ _ hne)
    obtain ⟨i, hi⟩ := this
    apply Finset.prod_eq_zero (Finset.mem_univ s)
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    apply Matrix.det_eq_zero_of_row_eq_zero i
    intro k
    simp [Matrix.diagonal_apply_ne _ (hi k).symm]
end PI.IsoInvMetricW
