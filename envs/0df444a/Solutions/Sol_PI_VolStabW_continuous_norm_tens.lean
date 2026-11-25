-- Prove2me | solution 1 for PI.VolStabW.continuous_norm_tens
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:59:34.516422+00:00
-- url     : https://prove2.me/submissions/1657b726-6b38-4805-94d7-e0d648376b85

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
theorem _root_.solution : Continuous (fun x : R ⊗[F] E => Algebra.norm R x) := by
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (R ⊗[F] E) := IsModuleTopology.isTopologicalRing R (R ⊗[F] E)
  let bE := Module.finBasis F E
  let b := Algebra.TensorProduct.basis R bE
  have he : (fun x : R ⊗[F] E => Algebra.norm R x) = fun x => (Algebra.leftMulMatrix b x).det := by
    funext x
    exact Algebra.norm_eq_matrix_det b x
  rw [he]
  apply Continuous.matrix_det
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have h1 : (fun x => Algebra.leftMulMatrix b x i j) =
      fun x => (b.coord i ∘ₗ LinearMap.mulRight R (b j)) x := by
    funext x
    simp [Algebra.leftMulMatrix_eq_repr_mul]
  rw [h1]
  exact IsModuleTopology.continuous_of_linearMap _
end PI.VolStabW
