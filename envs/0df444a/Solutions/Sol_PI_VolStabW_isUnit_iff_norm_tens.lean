-- Prove2me | solution 1 for PI.VolStabW.isUnit_iff_norm_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:03:46.616056+00:00
-- url     : https://prove2.me/submissions/a49cbbf7-6f88-44e0-8302-22ab4efffdbe

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
namespace PI.VolStabW
theorem _root_.solution (x : R ⊗[F] E) : IsUnit x ↔ IsUnit (Algebra.norm R x) := by
  rw [Algebra.norm_apply, ← LinearMap.isUnit_iff_isUnit_det]
  constructor
  · intro hx
    exact hx.map (Algebra.lmul R (R ⊗[F] E))
  · intro h
    obtain ⟨y, hy⟩ := ((Module.End.isUnit_iff _).1 h).2 1
    exact ⟨⟨x, y, hy, by rw [mul_comm]; exact hy⟩, rfl⟩
end PI.VolStabW
