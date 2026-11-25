-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.hermMap_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:39:41.610075+00:00
-- url     : https://prove2.me/submissions/c5b14adc-bb35-4342-b938-46eafe48f8af

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_conjT_one
import Theorems.Thm_PI_DegenerateSiegelWeil_Scale_hermMap_coe

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n M : ℕ}
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (S : HermR R σ n) : hermMap R σ hσ 1 S = S := by
  apply Subtype.ext
  simp [hermMap_coe, conjT_one]
end PI.DegenerateSiegelWeil.Scale
