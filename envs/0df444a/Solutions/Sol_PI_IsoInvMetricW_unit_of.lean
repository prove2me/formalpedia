-- Prove2me | solution 1 for PI.IsoInvMetricW.unit_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:14.06213+00:00
-- url     : https://prove2.me/submissions/ce2df649-c5b7-4c94-9909-ab762766d00c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_eq
import Theorems.Thm_PI_IsoInvMetricW_eStar
import Theorems.Thm_PI_IsoInvMetricW_e_one

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
theorem _root_.solution (hE : EMul) : Unit := by
  intro Lt _ _ N nu k hk φ ψ
  have hkk : ∀ z, star (k z) * k z = 1 := fun z => Matrix.mem_unitaryGroup_iff'.mp (hk z)
  have h1 : ∀ J J' : ColChoice N nu,
      ∑ I, starRingEnd ℂ (E nu k I J) * E nu k I J' = if J = J' then 1 else 0 := by
    intro J J'
    simp only [eStar]
    rw [hE]
    exact e_one _ hkk J J'
  have step : ∀ J J' : ColChoice N nu, ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') =
      star (φ J) * ψ J' * (if J = J' then 1 else 0) := by
    intro J J'
    rw [← h1 J J', Finset.mul_sum]
    refine Finset.sum_congr rfl fun I _ => ?_
    rw [star_mul', starRingEnd_apply]
    ring
  unfold ipl
  simp only [vnuMap_eq]
  calc ∑ I, star (∑ J, E nu k I J * φ J) * ∑ J', E nu k I J' * ψ J'
      = ∑ I, ∑ J, ∑ J', star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        refine Finset.sum_congr rfl fun I _ => ?_
        rw [star_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ J, ∑ J', ∑ I, star (E nu k I J * φ J) * (E nu k I J' * ψ J') := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun J _ => ?_
        rw [Finset.sum_comm]
    _ = ∑ J, star (φ J) * ψ J := by
        refine Finset.sum_congr rfl fun J _ => ?_
        simp only [step, mul_ite, mul_one, mul_zero]
        rw [Finset.sum_ite_eq]
        simp
end PI.IsoInvMetricW
