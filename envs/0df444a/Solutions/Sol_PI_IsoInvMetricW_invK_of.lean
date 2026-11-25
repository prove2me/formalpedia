-- Prove2me | solution 1 for PI.IsoInvMetricW.invK_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:03:08.012999+00:00
-- url     : https://prove2.me/submissions/a1cf6576-5f07-4cda-a903-ee53747a6b41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_eq
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
theorem _root_.solution (hE : EMul) : InvK := by
  intro Lt _ _ N nu k hk φ
  have hkk : ∀ z, k z * star (k z) = 1 := fun z => Matrix.mem_unitaryGroup_iff.mp (hk z)
  funext I
  have h1 : ∀ K, ∑ J, E nu k I J * E nu (fun z => star (k z)) J K = if I = K then 1 else 0 := by
    intro K
    rw [hE]
    exact e_one _ hkk I K
  simp only [vnuMap_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [← mul_assoc, ← Finset.sum_mul, h1, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq]
  simp
end PI.IsoInvMetricW
