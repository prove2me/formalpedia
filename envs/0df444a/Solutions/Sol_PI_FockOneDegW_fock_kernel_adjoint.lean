-- Prove2me | solution 1 for PI.FockOneDegW.fock_kernel_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:54:08.045895+00:00
-- url     : https://prove2.me/submissions/44cc4d2b-4f84-40e0-9833-aa94237ad698

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedDefs
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_FockOperatorsKernel
import Definitions.Def_Formalism_PeriodIntegrals_OrbitalBoundsConclusion_FockRaiseLow
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_RedOps
import Theorems.Thm_PI_FockOneDegW_RedOps_inner_posOp
import Theorems.Thm_PI_FockOneDegW_RedOps_inner_negOp
import Theorems.Thm_FockRL_sameBlock_symm
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left
import Theorems.Thm_FockRaiseLowInner_fockInner_add_right
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_left
import Theorems.Thm_FockRaiseLowInner_fockInner_neg_right
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_left
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_right
import Theorems.Thm_PI_FockOneDegW_fock_operators_kernel


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix FockH1Action MvPolynomial FockRaiseLowInner
open PI PI.FockOneDegW
open PI.FockOneDegW.RedOps
namespace PI.FockOneDegW
theorem _root_.solution : KAdj := by
  intro p q r s a b hab P Q
  have hba : sameBlock b a := FockRL.sameBlock_symm hab
  rw [fock_operators_kernel p q r s a b hab, fock_operators_kernel p q r s b a hba]
  simp only [sub_eq_add_neg, LinearMap.add_apply, LinearMap.neg_apply, fockInner_add_right,
    fockInner_add_left, fockInner_neg_right, fockInner_neg_left, inner_posOp a b hab,
    inner_negOp b a hba]
  by_cases h : a = b
  · subst h
    simp [fockInner_smul_right, fockInner_smul_left]
  · simp [h, Ne.symm h, fockInner_zero_right, fockInner_zero_left]
end PI.FockOneDegW
