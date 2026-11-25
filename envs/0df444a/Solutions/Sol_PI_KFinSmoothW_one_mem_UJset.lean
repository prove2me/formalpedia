-- Prove2me | solution 1 for PI.KFinSmoothW.one_mem_UJset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:48:49.566625+00:00
-- url     : https://prove2.me/submissions/a3490573-02fc-4897-93d6-78b3e4856cb0

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_UnitaryModelOfMultiplicityGardingDensity
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_KFiniteSmoothVectors_DenseWeakVectors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff
noncomputable section
open PI PI.KFinSmoothW
open PI.UpqRep
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
namespace PI.KFinSmoothW
theorem _root_.solution : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  exact (UJ ε).one_mem
end PI.KFinSmoothW
