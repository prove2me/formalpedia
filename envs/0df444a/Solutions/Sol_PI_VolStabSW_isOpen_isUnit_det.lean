-- Prove2me | solution 1 for PI.VolStabSW.isOpen_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T11:20:30.698115+00:00
-- url     : https://prove2.me/submissions/3cfa6f2d-e476-4f3c-ae3d-693c93eefa10

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Theorems.Thm_PI_VolStabSW_isOpen_units_tens

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
theorem _root_.solution (h : IsOpen {r : R | IsUnit r}) (n : ℕ) :
    IsOpen {S : Matrix (Fin n) (Fin n) (R ⊗[F] E) | IsUnit S.det} := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  exact (isOpen_units_tens R h).preimage (continuous_id.matrix_det)
end PI.VolStabSW
