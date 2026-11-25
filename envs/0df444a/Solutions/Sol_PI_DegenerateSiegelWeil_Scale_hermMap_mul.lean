-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.hermMap_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:35:03.012945+00:00
-- url     : https://prove2.me/submissions/9d374e7a-506b-4cc4-ae0e-69ea817180e9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_IsFibreFamilyReindex
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SiegelWeilVolume_MulTupApplyEqSum
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
theorem _root_.solution (hσ : ∀ x, σ (σ x) = x) (D₁ D₂ : Matrix (Fin n) (Fin n) (R ⊗[F] E))
    (S : HermR R σ n) : hermMap R σ hσ D₁ (hermMap R σ hσ D₂ S) = hermMap R σ hσ (D₂ * D₁) S := by
  apply Subtype.ext
  simp only [hermMap_coe, conjT_mul, Matrix.mul_assoc]
end PI.DegenerateSiegelWeil.Scale
