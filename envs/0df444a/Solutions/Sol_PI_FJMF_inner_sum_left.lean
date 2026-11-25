-- Prove2me | solution 1 for PI.FJMF.inner_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:38:31.330064+00:00
-- url     : https://prove2.me/submissions/a5badeb7-7a0e-48cd-860f-d4339f2f78d4

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_CauchyHW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_LoweringPartRightActionInlInr
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockDegreeOne_EqZeroOfFockInnerSelfRe
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockJointMultiplicity_BlockDegreeAntitone
import Theorems.Thm_FockRaiseLowInner_fockInner_add_left
import Theorems.Thm_FockRaiseLowInner_fockInner_zero_left


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
theorem _root_.solution {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  induction t using Finset.cons_induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, FockRaiseLowInner.fockInner_zero_left]
  | cons i t hi ih =>
    rw [Finset.sum_cons, Finset.sum_cons, FockRaiseLowInner.fockInner_add_left, ih]
end PI.FJMF
