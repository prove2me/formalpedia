-- Prove2me | solution 1 for PI.VolStabW.isOpen_units_Ainf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:12:52.149719+00:00
-- url     : https://prove2.me/submissions/5a7f9e48-56ad-4ba3-8659-2a9ffe30f302

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_VolFromSW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_T2SpaceTensorProductFiniteExtension
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
variable (F : Type) [Field F] [NumberField F]
namespace PI.VolStabW
theorem _root_.solution : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  have e : {x : InfiniteAdeleRing F | IsUnit x} =
      ⋂ v, (fun x : InfiniteAdeleRing F => x v) ⁻¹' {0}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    exact (Pi.isUnit_iff (M := fun v : InfinitePlace F => v.Completion) (x := x)).trans
      (forall_congr' fun v => isUnit_iff_ne_zero)
  rw [e]
  exact isOpen_iInter_of_finite fun v => isOpen_compl_singleton.preimage (continuous_apply v)
end PI.VolStabW
