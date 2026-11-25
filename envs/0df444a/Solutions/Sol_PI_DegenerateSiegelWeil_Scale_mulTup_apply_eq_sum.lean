-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.mulTup_apply_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:17.337992+00:00
-- url     : https://prove2.me/submissions/41e2cd5b-1a8d-4bca-98d9-94ec532eb38a

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
theorem _root_.solution (D : Matrix (Fin n) (Fin n) K) (X : Fin n → Fin M → K) (j : Fin n) :
    mulTup D X j = ∑ k, D k j • X k := by
  funext i
  simp [mulTup, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
end PI.DegenerateSiegelWeil.Scale
