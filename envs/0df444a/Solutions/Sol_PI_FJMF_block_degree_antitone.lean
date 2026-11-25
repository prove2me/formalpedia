-- Prove2me | solution 1 for PI.FJMF.block_degree_antitone
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:09:13.405393+00:00
-- url     : https://prove2.me/submissions/86be957b-d592-4911-ad58-198ba712cdea

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Theorems.Thm_PI_FJMF_comm_eq
import Theorems.Thm_PI_FJMF_euler_row
import Theorems.Thm_PI_FJMF_bRow_adj
import Theorems.Thm_FockRaiseLowInner_fockInner_smul_right
import Theorems.Thm_PI_FockOneDegW_Inner_eq_zero_of_fockInner_self_re
import Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_im
import Theorems.Thm_PI_FockOneDegW_Inner_fockInner_self_re_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial FockH1Action
open PI PI.FJMF
namespace PI.FJMF
theorem _root_.solution : BlockAntitone := by
  intro σ m n ι hι α P hP hE hdeg a b hab
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  · have hc := comm_eq ι hι a b P
    rw [hE a b h, map_zero, sub_zero, euler_row ι a (α a) P (fun e he => hdeg e he a),
      euler_row ι b (α b) P (fun e he => hdeg e he b)] at hc
    have hadj := bRow_adj ι a b P (PI.FJM.bRow ι b a P)
    rw [hc, ← sub_smul, FockRaiseLowInner.fockInner_smul_right] at hadj
    have h1 := PI.FockOneDegW.Inner.fockInner_self_re_nonneg (PI.FJM.bRow ι b a P)
    rw [hadj] at h1
    have hre := PI.FockOneDegW.Inner.fockInner_self_re_nonneg P
    have him := PI.FockOneDegW.Inner.fockInner_self_im P
    have hpos : 0 < (fockInner P P).re := lt_of_le_of_ne hre
      (fun h0 => hP (PI.FockOneDegW.Inner.eq_zero_of_fockInner_self_re P h0.symm))
    rw [Complex.mul_re, him, mul_zero, sub_zero] at h1
    simp only [Complex.sub_re, Complex.natCast_re] at h1
    have hlt : (α b : ℝ) ≤ α a := by nlinarith
    exact_mod_cast hlt
end PI.FJMF
