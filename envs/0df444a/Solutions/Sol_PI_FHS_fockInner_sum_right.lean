-- Prove2me | solution 1 for PI.FHS.fockInner_sum_right
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:36:15.910339+00:00
-- url     : https://prove2.me/submissions/03c7f746-c87c-4b88-9021-740ac4ad3d71

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Theorems.Thm_PI_FHS_fockInner_add_right
import Theorems.Thm_PI_FHS_fockInner_zero_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix FockH1Action
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution {ι : Type*} (t : Finset ι) (f : ι → MvPolynomial σ ℂ)
    (P : MvPolynomial σ ℂ) :
    fockInner P (∑ i ∈ t, f i) = ∑ i ∈ t, fockInner P (f i) := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_right]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_right, ih]
end PI.FHS
