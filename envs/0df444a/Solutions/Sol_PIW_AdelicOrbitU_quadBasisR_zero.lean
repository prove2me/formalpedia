-- Prove2me | solution 1 for PIW.AdelicOrbitU.quadBasisR_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:04:09.725733+00:00
-- url     : https://prove2.me/submissions/3c30703a-3a70-4cc3-a2c1-0facd05c47cb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Theorems.Thm_PIW_AdelicOrbitU_quadBasis_coe

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
theorem _root_.solution : quadBasisR h2 hli R 0 = (1 : R) ⊗ₜ[F] (1 : E) := by
  first
  | (unfold quadBasisR; rw [Algebra.TensorProduct.basis_apply, quadBasis_coe]; rfl)
  | simp [quadBasisR, quadBasis_coe]
end PIW.AdelicOrbitU
