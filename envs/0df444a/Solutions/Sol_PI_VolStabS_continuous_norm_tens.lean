-- Prove2me | solution 1 for PI.VolStabS.continuous_norm_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:50:31.63372+00:00
-- url     : https://prove2.me/submissions/db75c735-0b05-4ca5-8475-b87e79441ea3

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
theorem _root_.solution : Continuous (fun x : R ⊗[F] E => Algebra.norm R x) := by
  classical
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  have hn : (fun x : R ⊗[F] E => Algebra.norm R x) = fun x => (Algebra.leftMulMatrix b x).det :=
    funext fun x => Algebra.norm_eq_matrix_det b x
  rw [hn]
  refine Continuous.matrix_det (continuous_pi fun i => continuous_pi fun j => ?_)
  simp only [Algebra.leftMulMatrix_eq_repr_mul]
  exact IsModuleTopology.continuous_of_linearMap
    ((b.coord i).comp (LinearMap.mulRight R (b j)))
end PI.VolStabS
