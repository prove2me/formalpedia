-- Prove2me | solution 1 for PI.NcVal.OmVc2.mulTup_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:22:23.666708+00:00
-- url     : https://prove2.me/submissions/125cada0-a51a-41a6-bfb0-d02d40ccdc5d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_AddEquivAddHaarCharEqOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ValuationLocalVolumes_MulTupDiagonal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.NcVal PI.NcVal.OmVc2
open MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.DegenerateSiegelWeil.Scale PI.VolStabSW PI.VolStabSW.TensAllW
open scoped NNReal TensorProduct
variable {K : Type} [CommRing K] {a M : ℕ}
namespace PI.NcVal.OmVc2
theorem _root_.solution (f : Fin a → K) (X : Fin a → Fin M → K) :
    mulTup (Matrix.diagonal f) X = fun j i => f j * X j i := by
  funext j i
  simp [mulTup, Matrix.diagonal_apply, ite_mul, Finset.sum_ite_eq']
end PI.NcVal.OmVc2
