-- Prove2me | solution 1 for PI.VolStabW.continuous_gramR_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:59:30.796023+00:00
-- url     : https://prove2.me/submissions/c32a8b5b-e8e8-4dec-83ee-4e9f3edbb6c2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
variable [LocallyCompactSpace R] [T2Space R]
namespace PI.VolStabW
theorem _root_.solution (σ : E →ₐ[F] E) {M n : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin n) : Continuous (fun X : Fin n → Fin M → R ⊗[F] E => gramR R σ J X a b) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  have hsig : Continuous (sigR R σ) := by
    have e : ⇑(sigR R σ) = ⇑(LinearMap.baseChange R σ.toLinearMap) := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul r e => simp [sigR]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _
  unfold gramR hR Formalism.UG.hform
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact ((hsig.comp ((continuous_apply i).comp (continuous_apply a))).mul continuous_const).mul
    ((continuous_apply j).comp (continuous_apply b))
end PI.VolStabW
