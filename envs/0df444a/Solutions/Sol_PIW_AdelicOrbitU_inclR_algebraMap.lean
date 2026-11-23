-- Prove2me | solution 1 for PIW.AdelicOrbitU.inclR_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:45.145448+00:00
-- url     : https://prove2.me/submissions/ee50bac0-ad0d-4723-ba4b-98b7a7747dc3

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_AdelicOrbitU
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_UnitChoice
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicUnitaryOrbits_InclRAlgebraMap

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
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct
variable {F E : Type} [Field F] [Field E] [Algebra F E]
namespace PIW.AdelicOrbitU
theorem _root_.solution (R : Type) [CommRing R] [Algebra F R] (b : F) :
    inclR R (algebraMap F E b) = algebraMap F (R ⊗[F] E) b :=
  (Algebra.TensorProduct.includeRight : E →ₐ[F] R ⊗[F] E).commutes b
end PIW.AdelicOrbitU
