-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_coord_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:11.679465+00:00
-- url     : https://prove2.me/submissions/ec1854bb-6c95-4f69-b8c2-a3a2123b076f

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
theorem _root_.solution (a b : R) :
    ⇑((quadBasisR h2 hli R).repr (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ)) = ![a, b] := by
  have e : a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ =
      a • quadBasisR h2 hli R 0 + b • quadBasisR h2 hli R 1 := by
    rw [quadBasisR_zero, quadBasisR_one, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      smul_eq_mul, smul_eq_mul, mul_one, mul_one]
  rw [e, map_add, map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self]
  funext i
  fin_cases i <;> simp
end PIW.AdelicOrbitU
