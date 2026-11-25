-- Prove2me | solution 1 for PI.FHS.fockInner_self_re_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:38:15.649123+00:00
-- url     : https://prove2.me/submissions/ac3eac8f-c640-460b-8457-377a232522df

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_fockInner_self

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
theorem _root_.solution (P : MvPolynomial σ ℂ) : 0 ≤ (FockH1Action.fockInner P P).re := by
  rw [fockInner_self, Complex.re_sum]
  refine Finset.sum_nonneg (fun α _ => ?_)
  rw [Complex.ofReal_re]
  exact mul_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _)
end PI.FHS
