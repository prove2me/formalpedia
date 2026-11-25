-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_coord_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T11:20:51.117563+00:00
-- url     : https://prove2.me/submissions/37919867-4eb4-4164-bdb3-31c5c7f08c16

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional
import Theorems.Thm_PIW_AdelicOrbitU_quad_coord_eq

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
theorem _root_.solution (a b : R) : (quadBasisR h2 hli R).repr (a ⊗ₜ[F] (1 : E) + b ⊗ₜ[F] θ) 0 = a := by
  have h := congrFun (quad_coord_eq h2 hli R a b) 0
  simpa using h
end PIW.AdelicOrbitU
