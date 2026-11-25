-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.theta_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:03:56.672792+00:00
-- url     : https://prove2.me/submissions/c084764e-3a65-4edf-bf70-da45a9cdb073

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective
import Theorems.Thm_PI_ParahoricIdxZ_W_reindex_theta

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open PI PI.ParahoricIdxZ PI.ParahoricIdxZ.W
variable {F : Type} [Field F] (O : Subring F) (ϖ : F)
namespace PI.ParahoricIdxZ.W
theorem _root_.solution {a t : ℕ} {R : Type} {A A' : Matrix (Fin a) (Fin a) R}
    {B B' : Matrix (Fin a) (Fin t) R} {C C' : Matrix (Fin t) (Fin a) R}
    {D D' : Matrix (Fin t) (Fin t) R} (h : theta A B C D = theta A' B' C' D') :
    A = A' ∧ B = B' ∧ C = C' ∧ D = D' := by
  have h2 := congrArg (Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm) h
  rw [reindex_theta, reindex_theta] at h2
  exact Matrix.fromBlocks_inj.mp h2
end PI.ParahoricIdxZ.W
