-- Prove2me | solution 1 for PI.VolStabS.continuous_gramR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:28.159858+00:00
-- url     : https://prove2.me/submissions/ad1b29e9-0721-4313-a903-317188582207

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]
namespace PI.VolStabS
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X a b) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R _
  let sL : R ⊗[F] E →ₗ[R] R ⊗[F] E :=
    { toFun := sigR R σ
      map_add' := map_add _
      map_smul' := fun r x => by
        rw [RingHom.id_apply, Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        simp [sigR, Algebra.TensorProduct.algebraMap_apply] }
  have hs : Continuous (sigR R σ) := IsModuleTopology.continuous_of_linearMap sL
  simp only [gramR, hR, Formalism.UG.hform]
  exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ =>
    ((hs.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
      ((continuous_apply j).comp (continuous_apply b))
end PI.VolStabS
