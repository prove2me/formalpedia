-- Prove2me | solution 1 for PI.VolStabSW.isOpen_units_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:08:30.079018+00:00
-- url     : https://prove2.me/submissions/6a1495d5-8edd-4b62-9be4-21ae9682defa

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Theorems.Thm_PI_VolStabSW_continuous_norm_tens
import Theorems.Thm_PI_VolStabSW_isUnit_iff_norm_tens

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
theorem _root_.solution (h : IsOpen {r : R | IsUnit r}) :
    IsOpen {x : R ⊗[F] E | IsUnit x} := by
  have e : {x : R ⊗[F] E | IsUnit x} = (fun x => Algebra.norm R x) ⁻¹' {r : R | IsUnit r} := by
    ext x
    exact isUnit_iff_norm_tens R x
  rw [e]
  exact h.preimage (continuous_norm_tens (F := F) (E := E) R)
end PI.VolStabSW
