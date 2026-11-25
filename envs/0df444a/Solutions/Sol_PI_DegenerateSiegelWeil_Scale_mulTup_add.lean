-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.mulTup_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:13.332529+00:00
-- url     : https://prove2.me/submissions/80a9ef3c-b11e-4547-b957-2bd9d2230e9e

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
theorem _root_.solution (D : Matrix (Fin n) (Fin n) K) (X Y : Fin n → Fin M → K) :
    mulTup D (X + Y) = mulTup D X + mulTup D Y := by
  funext j i
  simp [mulTup, mul_add, Finset.sum_add_distrib]
end PI.DegenerateSiegelWeil.Scale
