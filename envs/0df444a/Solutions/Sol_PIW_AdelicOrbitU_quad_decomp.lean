-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:00.785903+00:00
-- url     : https://prove2.me/submissions/be801cef-4602-4934-8782-8ac032b86546

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Theorems.Thm_PIW_AdelicOrbitU_quadBasisR_zero
import Theorems.Thm_PIW_AdelicOrbitU_quadBasisR_one

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
namespace PIW.AdelicOrbitU
theorem _root_.solution (z : R ⊗[F] E) :
    z = ((quadBasisR h2 hli R).repr z 0) ⊗ₜ[F] (1 : E) + ((quadBasisR h2 hli R).repr z 1) ⊗ₜ[F] θ := by
  conv_lhs => rw [← (quadBasisR h2 hli R).sum_repr z]
  rw [Fin.sum_univ_two, quadBasisR_zero, quadBasisR_one, TensorProduct.smul_tmul',
    TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, mul_one, mul_one]
end PIW.AdelicOrbitU
