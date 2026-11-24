-- Prove2me | solution 1 for PI.FHS.fockInner_neg_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:33.030855+00:00
-- url     : https://prove2.me/submissions/837f4a4b-970d-4e03-83d7-85ff393c1ff0

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_fockInner_eq_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PI PI.FHS
variable {σ : Type*}
namespace PI.FHS
theorem _root_.solution (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (-P) Q = - FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right (-P) Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_neg, map_neg]
  ring
end PI.FHS
