-- Prove2me | solution 1 for PI.VolStabSW.continuous_norm_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:54:30.941087+00:00
-- url     : https://prove2.me/submissions/b1e86582-84df-4d14-8568-170e485aa325

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
theorem _root_.solution : Continuous (fun x : R ⊗[F] E => Algebra.norm R x) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have hc : Continuous (Algebra.leftMulMatrix b) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap
  have e : (fun x : R ⊗[F] E => Algebra.norm R x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [e]
  exact hc.matrix_det
end PI.VolStabSW
