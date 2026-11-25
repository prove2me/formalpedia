-- Prove2me | solution 1 for PI.FHS.fockInner_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:49:48.577055+00:00
-- url     : https://prove2.me/submissions/864c0d6a-400f-4d73-9dc9-75e2d84a1d3f

import Definitions.Def_Formalism_PeriodIntegrals_JointBlockShapes_MinusPart
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_FockHarmonicSplitting_FockInnerSelfReNonneg
import Theorems.Thm_PI_FHS_fockInner_conj
import Theorems.Thm_PI_FHS_fockInner_X_mul

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
theorem _root_.solution [Fintype σ] (l : σ) (P Q : MvPolynomial σ ℂ) :
    FockH1Action.fockInner (pderiv l P) Q = FockH1Action.fockInner P (X l * Q) := by
  rw [← fockInner_conj (pderiv l P) Q, ← fockInner_X_mul l Q P, fockInner_conj]
end PI.FHS
