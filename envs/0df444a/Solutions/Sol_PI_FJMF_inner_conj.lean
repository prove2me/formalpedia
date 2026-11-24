-- Prove2me | solution 1 for PI.FJMF.inner_conj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:03:26.032573+00:00
-- url     : https://prove2.me/submissions/7139b011-1e7b-4b0f-921d-8615f3116e1d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Theorems.Thm_FockRaiseLowInner_fockInner_eq_sum_left
import Theorems.Thm_FockRaiseLowInner_wt_conj


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
variable {σ : Type}
namespace PI.FJMF
theorem _root_.solution (P Q : MvPolynomial σ ℂ) : fockInner Q P = starRingEnd ℂ (fockInner P Q) := by
  classical
  rw [FockRaiseLowInner.fockInner_eq_sum_left Q P (P.support ∪ Q.support) Finset.subset_union_right,
    FockRaiseLowInner.fockInner_eq_sum_left P Q (P.support ∪ Q.support) Finset.subset_union_left, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, map_mul, Complex.conj_conj, FockRaiseLowInner.wt_conj]
  ring
end PI.FJMF
