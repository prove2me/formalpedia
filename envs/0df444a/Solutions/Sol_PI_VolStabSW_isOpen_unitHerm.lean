-- Prove2me | solution 1 for PI.VolStabSW.isOpen_unitHerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:35:59.760356+00:00
-- url     : https://prove2.me/submissions/47f91e8a-f5bd-4f84-b4dd-77e556b7f032

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Theorems.Thm_PI_VolStabSW_isOpen_isUnit_det

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
  [LocallyCompactSpace R] [T2Space R]
namespace PI.VolStabSW
theorem _root_.solution (h : IsOpen {r : R | IsUnit r}) (σ : E →ₐ[F] E) (n : ℕ) :
    IsOpen {S : HermR R σ n | IsUnit (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)).det} := (isOpen_isUnit_det R h n).preimage continuous_subtype_val
end PI.VolStabSW
