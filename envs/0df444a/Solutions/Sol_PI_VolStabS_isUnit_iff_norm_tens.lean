-- Prove2me | solution 1 for PI.VolStabS.isUnit_iff_norm_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:51:02.907061+00:00
-- url     : https://prove2.me/submissions/667ddf63-cf82-4b3c-b608-8c0f3e8e15d0

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
namespace PI.VolStabS
theorem _root_.solution (x : R ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm R x) := by
  haveI : Module.Free R (R ⊗[F] E) :=
    Module.Free.of_basis (Algebra.TensorProduct.basis R (Module.finBasis F E))
  constructor
  · intro h
    exact h.map (Algebra.norm R)
  · intro h
    rw [Algebra.norm_apply] at h
    obtain ⟨u, hu⟩ := (LinearMap.isUnit_iff_isUnit_det _).2 h
    have h1 : (u : Module.End R (R ⊗[F] E)) ((↑u⁻¹ : Module.End R (R ⊗[F] E)) 1) = 1 := by
      rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]
    rw [hu] at h1
    exact isUnit_iff_exists_inv.2 ⟨_, h1⟩
end PI.VolStabS
