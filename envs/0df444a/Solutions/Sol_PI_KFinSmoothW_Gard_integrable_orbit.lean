-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.integrable_orbit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:56:11.041835+00:00
-- url     : https://prove2.me/submissions/dfd0bcc8-8d71-400d-a8c9-ccdaba1f1494

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
import Theorems.Thm_PI_KFinSmoothW_Gard_cont_orbit

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
theorem _root_.solution {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ)
    (Ψ : UJ ε → ℂ) (hΨ : Continuous Ψ) (hΨc : HasCompactSupport Ψ) (x : H) :
    Integrable (fun h => Ψ h • τ (umat h) x) (muG ε) := by
  exact (hΨ.smul (cont_orbit hτ x)).integrable_of_hasCompactSupport hΨc.smul_right
end PI.KFinSmoothW.Gard
