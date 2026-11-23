-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.reindex_theta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:37:29.386345+00:00
-- url     : https://prove2.me/submissions/cb65eb03-c3e6-4d78-bf07-6a529f11e704

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ParahoricIndexCount_ThetaInjective

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
theorem _root_.solution {a t : ℕ} {R : Type} (A : Matrix (Fin a) (Fin a) R)
    (B : Matrix (Fin a) (Fin t) R) (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R) :
    Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm (theta A B C D) =
      Matrix.fromBlocks A B C D := by
  ext x y
  simp [theta, Matrix.reindex_apply]
end PI.ParahoricIdxZ.W
