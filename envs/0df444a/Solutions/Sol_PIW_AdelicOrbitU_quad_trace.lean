-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:37:56.600436+00:00
-- url     : https://prove2.me/submissions/8cd120e6-72a9-4730-b862-b7c3561570d9

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Theorems.Thm_PIW_AdelicOrbitU_quadBasisR_zero
import Theorems.Thm_PIW_AdelicOrbitU_quadBasisR_one
import Theorems.Thm_PIW_AdelicOrbitU_quad_coord_zero
import Theorems.Thm_PIW_AdelicOrbitU_quad_coord_one
import Theorems.Thm_PIW_AdelicOrbitU_quad_tmul_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PIW PIW.AdelicOrbitU
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
variable {F E : Type} [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
  (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ])
  (R : Type) [CommRing R] [Algebra F R]
include h2 hli
namespace PIW.AdelicOrbitU
theorem _root_.solution {d : F} (hd : θ * θ = algebraMap F E d) (a b : R) :
    Algebra.trace R (R ⊗[F] E) (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) = 2 * a := by
  have e1 : (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) * ((1 : R) ⊗ₜ[F] θ) =
      (algebraMap F R d * b) ⊗ₜ[F] (1 : E) + a ⊗ₜ[F] θ := by
    simp only [add_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, hd,
      quad_tmul_algebraMap]
    abel
  rw [Algebra.trace_eq_matrix_trace (quadBasisR h2 hli R), Matrix.trace_fin_two,
    Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, quadBasisR_zero,
    quadBasisR_one, ← Algebra.TensorProduct.one_def, mul_one, e1, quad_coord_zero, quad_coord_one]
  ring
end PIW.AdelicOrbitU
