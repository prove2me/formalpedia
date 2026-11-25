-- Prove2me | solution 1 for PI.VolStabSW.isUnit_iff_norm_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:57:14.766904+00:00
-- url     : https://prove2.me/submissions/af184573-16f3-4a2e-bd95-8f1ecd9ed83b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
namespace PI.VolStabSW
theorem _root_.solution (x : R ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm R x) := by
  constructor
  · intro h
    exact h.map (Algebra.norm R)
  · intro h
    rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det] at h
    obtain ⟨u, hu⟩ := h
    have h1 : x * (↑u⁻¹ : Module.End R (R ⊗[F] E)) 1 = 1 := by
      have e := congrArg (fun f : Module.End R (R ⊗[F] E) => f 1) u.mul_inv
      simp only [Module.End.mul_apply, Module.End.one_apply] at e
      rw [hu] at e
      exact e
    exact ⟨⟨x, _, h1, by rw [mul_comm]; exact h1⟩, rfl⟩
end PI.VolStabSW
