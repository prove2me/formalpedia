-- Prove2me | solution 1 for PI.NMeasInv.UnitaryGroupMassFormula.hJ_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:56:41.150859+00:00
-- url     : https://prove2.me/submissions/b289ca9e-bf91-4ded-84b6-9f8758258879

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_NMeasInv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MeasureInverseContraction_AmatInvMul

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
open PI PI.NMeasInv PI.NMeasInv.UnitaryGroupMassFormula
variable {n r : ℕ} (ε : Fin n → Bool)
variable {ε} {e f : Fin r → Fin n → ℂ}
variable (hG : Gram ε e f)
include hG
omit hG
namespace PI.NMeasInv.UnitaryGroupMassFormula
theorem _root_.solution (M : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    hJ ε (M *ᵥ x) (M *ᵥ y) = star x ⬝ᵥ ((Mᴴ * Formalism.REAL.Jm ε * M) *ᵥ y) := by
  unfold hJ
  rw [Matrix.star_mulVec, Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]
end PI.NMeasInv.UnitaryGroupMassFormula
