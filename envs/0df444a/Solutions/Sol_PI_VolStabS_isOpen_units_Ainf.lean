-- Prove2me | solution 1 for PI.VolStabS.isOpen_units_Ainf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:45.558849+00:00
-- url     : https://prove2.me/submissions/b227355c-2c1f-404e-9c1e-e2222607fc7e

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabS
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabS
theorem _root_.solution : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  show IsOpen {x : (v : InfinitePlace F) → v.Completion | IsUnit x}
  have hs : {x : (v : InfinitePlace F) → v.Completion | IsUnit x} =
      Set.univ.pi fun v : InfinitePlace F => {y : v.Completion | IsUnit y} := by
    ext x
    simp [Pi.isUnit_iff]
  rw [hs]
  exact isOpen_set_pi Set.finite_univ fun v _ => Units.isOpen
end PI.VolStabS
