-- Prove2me | solution 1 for PIW.AdelicOrbitU.quadBasis_coe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:38.125772+00:00
-- url     : https://prove2.me/submissions/09937cf3-0ea5-4547-942a-5d01392c56ba

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
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)
namespace PIW.AdelicOrbitU
theorem _root_.solution (h2 : Module.finrank F E = 2) {θ : E} (hli : LinearIndependent F ![(1 : E), θ]) :
    ⇑(quadBasis h2 hli) = ![(1 : E), θ] := by
  first
  | exact coe_basisOfLinearIndependentOfCardEqFinrank hli _
  | (unfold quadBasis; exact coe_basisOfLinearIndependentOfCardEqFinrank hli _)
  | simp [quadBasis]
end PIW.AdelicOrbitU
