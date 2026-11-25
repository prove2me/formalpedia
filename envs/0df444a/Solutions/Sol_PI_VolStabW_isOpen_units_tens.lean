-- Prove2me | solution 1 for PI.VolStabW.isOpen_units_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:18:47.472268+00:00
-- url     : https://prove2.me/submissions/df3854c0-d6c1-4a2b-b164-a8f7db91b560

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Theorems.Thm_PI_VolStabW_continuous_norm_tens
import Theorems.Thm_PI_VolStabW_isUnit_iff_norm_tens

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
theorem _root_.solution (h : IsOpen {r : R | IsUnit r}) :
    IsOpen {x : R ⊗[F] E | IsUnit x} := by
  have e : {x : R ⊗[F] E | IsUnit x} = (fun x => Algebra.norm R x) ⁻¹' {r | IsUnit r} := by
    ext x
    exact isUnit_iff_norm_tens R x
  rw [e]
  exact h.preimage (continuous_norm_tens R)
end PI.VolStabW
