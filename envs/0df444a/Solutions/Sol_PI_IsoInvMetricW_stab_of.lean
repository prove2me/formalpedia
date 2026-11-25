-- Prove2me | solution 1 for PI.IsoInvMetricW.stab_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:57:41.018631+00:00
-- url     : https://prove2.me/submissions/cdcb4dd6-058b-48bc-a63a-2e840f2f1640

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_OeEqOfRangeSub
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InvariantMetricIsometry_VnuMapZero
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_add
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_smul
import Theorems.Thm_PI_IsoInvMetricW_vnuMap_zero

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
theorem _root_.solution (hM : HvMap) : Stab := by
  intro Lt _ _ N nu f φ hφ
  induction hφ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, rfl⟩ := hx
    rw [hM]
    exact Submodule.subset_span ⟨_, rfl⟩
  | zero => rw [vnuMap_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [vnuMap_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [vnuMap_smul]; exact Submodule.smul_mem _ a hx
end PI.IsoInvMetricW
