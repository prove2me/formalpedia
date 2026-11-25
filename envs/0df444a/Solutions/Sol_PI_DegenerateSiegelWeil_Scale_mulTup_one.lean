-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.mulTup_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:39.213841+00:00
-- url     : https://prove2.me/submissions/b7173aa6-401b-428f-acc3-f723a0cfdddc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.DegenerateSiegelWeil PI.DegenerateSiegelWeil.Scale
open MeasureTheory Topology Set Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolStabSW
open scoped ENNReal NNReal TensorProduct Matrix
variable {K : Type} [CommRing K] {n M : ℕ}
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (X : Fin n → Fin M → K) : mulTup (1 : Matrix (Fin n) (Fin n) K) X = X := by
  funext j i
  simp [mulTup, Matrix.one_apply]
end PI.DegenerateSiegelWeil.Scale
