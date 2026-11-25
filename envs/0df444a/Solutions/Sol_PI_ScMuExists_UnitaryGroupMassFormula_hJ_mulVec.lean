-- Prove2me | solution 1 for PI.ScMuExists.UnitaryGroupMassFormula.hJ_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:29:02.196949+00:00
-- url     : https://prove2.me/submissions/d0df8862-e66e-4e51-898d-9866297dc66d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_ScMuExists
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_InstDecomp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureDecomposition_ContinuousUMatApply

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
open PI PI.ScMuExists PI.ScMuExists.UnitaryGroupMassFormula
variable {n r : ℕ}
namespace PI.ScMuExists.UnitaryGroupMassFormula
theorem _root_.solution {ε : Fin n → Bool} {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g)
    (x y : Fin n → ℂ) : hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  have hg' : gᴴ * Formalism.REAL.Jm ε * g = Formalism.REAL.Jm ε := hg
  unfold hJ
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_vecMul, ← Matrix.mul_assoc, hg']
end PI.ScMuExists.UnitaryGroupMassFormula
