-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.umat_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:37.572344+00:00
-- url     : https://prove2.me/submissions/92c70166-a3f3-46c0-884d-a9d963905a26

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology Set Metric
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
open PI.KFinSmoothW.Gard
attribute [local instance] mMeas
attribute [local instance] mBorel
attribute [local instance] mBorelN
attribute [local instance] mLocCpt
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]
namespace PI.KFinSmoothW.Gard
theorem _root_.solution (γ : UJ ε) : umat γ⁻¹ = Jm ε * (umat γ)ᴴ * Jm ε := by
  exact coeMatrix_inv_eq ε γ
end PI.KFinSmoothW.Gard
