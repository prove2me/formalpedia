-- Prove2me | solution 1 for PI.FHS.fockInner_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:05:28.585812+00:00
-- url     : https://prove2.me/submissions/b27fe38e-ef29-45f6-a6a2-2668412d1816

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
theorem _root_.solution (c : ℂ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (c • P) Q = (starRingEnd ℂ) c * FockH1Action.fockInner P Q := by
  rw [fockInner_eq_sum_right (c • P) Q Q.support (Finset.Subset.refl _),
    fockInner_eq_sum_right P Q Q.support (Finset.Subset.refl _), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun α _ => ?_)
  simp only [coeff_smul, smul_eq_mul, map_mul]
  ring
end PI.FHS
