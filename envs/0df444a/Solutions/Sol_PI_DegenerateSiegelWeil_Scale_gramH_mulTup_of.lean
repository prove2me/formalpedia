-- Prove2me | solution 1 for PI.DegenerateSiegelWeil.Scale.gramH_mulTup_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:34:58.46929+00:00
-- url     : https://prove2.me/submissions/715a808e-ecc3-4600-8e37-143917e7cb7f

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
namespace PI.DegenerateSiegelWeil.Scale
theorem _root_.solution (hG : GramMulTup) {F E : Type} [Field F] [Field E] [Algebra F E]
    (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) {n M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (hJ : ∀ i j, σ (J j i) = J i j)
    (D : Matrix (Fin n) (Fin n) (R ⊗[F] E)) (X : Fin n → Fin M → R ⊗[F] E) :
    PI.VolStabSW.gramH R σ hσ J hJ (mulTup D X) =
      hermMap R σ hσ D (PI.VolStabSW.gramH R σ hσ J hJ X) := by
  apply Subtype.ext
  rw [hermMap_coe]
  exact hG F E R σ n M J D X
end PI.DegenerateSiegelWeil.Scale
