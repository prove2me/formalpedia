-- Prove2me | solution 1 for PI.ParahoricIdxZ.W.theta_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:02:14.735859+00:00
-- url     : https://prove2.me/submissions/b87aac6c-f563-43dc-a6d2-2704657e1cac

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
    (B : Matrix (Fin a) (Fin t) R) (C : Matrix (Fin t) (Fin a) R) (D : Matrix (Fin t) (Fin t) R)
    (x y : Fin a ⊕ Fin t) :
    theta A B C D (finSumFinEquiv x) (finSumFinEquiv y) = Matrix.fromBlocks A B C D x y := by
  simp [theta, Matrix.reindex_apply]
end PI.ParahoricIdxZ.W
