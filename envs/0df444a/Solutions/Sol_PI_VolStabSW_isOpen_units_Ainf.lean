-- Prove2me | solution 1 for PI.VolStabSW.isOpen_units_Ainf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:43:29.642212+00:00
-- url     : https://prove2.me/submissions/20815af1-705a-43c9-8428-509d519b655b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabSW
theorem _root_.solution : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  have e : {x : InfiniteAdeleRing F | IsUnit x} = ⋂ v, {x : InfiniteAdeleRing F | x v ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    exact Pi.isUnit_iff.trans (forall_congr' fun v => isUnit_iff_ne_zero)
  rw [e]
  exact isOpen_iInter_of_finite fun v => isOpen_ne_fun (continuous_apply v) continuous_const
end PI.VolStabSW
