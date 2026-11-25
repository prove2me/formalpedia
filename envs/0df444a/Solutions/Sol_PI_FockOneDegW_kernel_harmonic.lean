-- Prove2me | solution 1 for PI.FockOneDegW.kernel_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:14:10.517278+00:00
-- url     : https://prove2.me/submissions/93d48ed3-b562-4e89-9715-f498a1a8b742

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_ExistsMonomialWeight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_KernelHarmonic
import Theorems.Thm_PI_FockOneDegW_RedOps_lowOp_posOp
import Theorems.Thm_PI_FockOneDegW_RedOps_lowOp_negOp
import Theorems.Thm_PI_FockOneDegW_fock_operators_kernel
import Theorems.Thm_PI_FockOneDegW_harmIff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial
open PI PI.FockOneDegW
open PI.FockOneDegW.RedOps
namespace PI.FockOneDegW
theorem _root_.solution : KHarm := by
  intro p q r s a b hab P hP
  rw [harmIff] at hP ⊢
  intro c d hcd
  rw [fock_operators_kernel p q r s a b hab]
  simp only [LinearMap.add_apply, LinearMap.sub_apply, map_add, map_sub, lowOp_posOp c d hcd,
    lowOp_negOp c d hcd a b hab, hP c d hcd, map_zero, zero_add, sub_self]
  split_ifs <;> simp [hP c d hcd]
end PI.FockOneDegW
