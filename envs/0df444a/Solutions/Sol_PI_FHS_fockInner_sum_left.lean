-- Prove2me | solution 1 for PI.FHS.fockInner_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:44.28239+00:00
-- url     : https://prove2.me/submissions/694d0fee-1b90-4094-ac9d-d7c7810efc3f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_ConjTransposeOneKronecker
import Theorems.Thm_PI_FHS_fockInner_add_left
import Theorems.Thm_PI_FHS_fockInner_zero_left


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
    (Q : MvPolynomial σ ℂ) :
    fockInner (∑ i ∈ t, f i) Q = ∑ i ∈ t, fockInner (f i) Q := by
  classical
  refine Finset.induction_on t ?_ ?_
  · simp only [Finset.sum_empty, fockInner_zero_left]
  · intro i t hi ih
    rw [Finset.sum_insert hi, Finset.sum_insert hi, fockInner_add_left, ih]
end PI.FHS
