-- Prove2me | solution 1 for PI.FHS.fockInner_add_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:26.476815+00:00
-- url     : https://prove2.me/submissions/c5a5fd09-462a-4465-b143-a9ba329051e1

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
theorem _root_.solution (P P' Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (P + P') Q = FockH1Action.fockInner P Q + FockH1Action.fockInner P' Q := by
  rw [fockInner_eq_sum_right (P + P') Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P' Q Q.support (Finset.Subset.refl _),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  rw [coeff_add, map_add]
  ring
end PI.FHS
