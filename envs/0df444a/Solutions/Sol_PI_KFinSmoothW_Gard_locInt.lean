-- Prove2me | solution 1 for PI.KFinSmoothW.Gard.locInt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:33.640347+00:00
-- url     : https://prove2.me/submissions/e8150c2d-06bf-4e8e-a11f-4cfb9f5199c7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_Garding
import Theorems.Thm_PI_KFinSmoothW_Gard_umat_closedEmb
import Theorems.Thm_PI_KFinSmoothW_Gard_umat_measEmb
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
theorem _root_.solution {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (x : H) :
    LocallyIntegrable (fun t => τ t x) (Measure.map umat (muG ε)) := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro K hK
  rw [(umat_measEmb ε).integrableOn_map_iff]
  exact (cont_orbit hτ x).continuousOn.integrableOn_compact ((umat_closedEmb ε).isCompact_preimage hK)
end PI.KFinSmoothW.Gard
