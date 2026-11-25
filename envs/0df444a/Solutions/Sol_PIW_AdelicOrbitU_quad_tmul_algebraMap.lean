-- Prove2me | solution 1 for PIW.AdelicOrbitU.quad_tmul_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:22:23.024752+00:00
-- url     : https://prove2.me/submissions/dc7ce37a-14ee-4bfe-ba61-0a725c58c525

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_QuadFiniteDimensional

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
theorem _root_.solution (x : R) (d : F) :
    x ⊗ₜ[F] (algebraMap F E d) = (algebraMap F R d * x) ⊗ₜ[F] (1 : E) := by
  rw [show algebraMap F E d = d • (1 : E) from Algebra.algebraMap_eq_smul_one d,
    ← TensorProduct.smul_tmul, Algebra.smul_def]
end PIW.AdelicOrbitU
