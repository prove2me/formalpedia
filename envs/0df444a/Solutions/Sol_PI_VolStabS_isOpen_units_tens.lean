-- Prove2me | solution 1 for PI.VolStabS.isOpen_units_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:03:38.742277+00:00
-- url     : https://prove2.me/submissions/571d2289-dde5-4757-b7f4-897fae0f3dce

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop
import Theorems.Thm_PI_VolStabS_continuous_norm_tens
import Theorems.Thm_PI_VolStabS_isUnit_iff_norm_tens

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
theorem _root_.solution (h : IsOpen {r : R | IsUnit r}) :
    IsOpen {x : R ⊗[F] E | IsUnit x} := by
  have hs : {x : R ⊗[F] E | IsUnit x} = (fun x => Algebra.norm R x) ⁻¹' {r : R | IsUnit r} :=
    Set.ext fun x => isUnit_iff_norm_tens R x
  rw [hs]
  exact h.preimage (continuous_norm_tens R)
end PI.VolStabS
