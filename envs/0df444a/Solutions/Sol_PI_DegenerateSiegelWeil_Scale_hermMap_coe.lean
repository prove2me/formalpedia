-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.hermMap_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:27:07.10156+00:00
-- url     : https://prove2.me/submissions/a0680d86-3145-4e83-8ffc-db6b78530541

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {n M : ℕ}
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (D : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) :
    (hermMap R σ hσ D S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) = conjT R σ D * S * D := rfl
end PI.DegenerateSiegelWeil.Scale
